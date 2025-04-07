package vct.col.rewrite.exc

import vct.col.ast._
import vct.col.util.AstBuildHelpers._
import RewriteHelpers._
import hre.util.ScopedStack
import vct.col.rewrite.exc.SwitchToGoto.CaseOutsideSwitch
import vct.col.origin.{LabelContext, Origin, PreferredName}
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder}
import vct.result.VerificationError.{SystemError, UserError}

import scala.collection.mutable.ArrayBuffer

case object SwitchToGoto extends RewriterBuilder {
  override def key: String = "switchToGoto"
  override def desc: String = "Translate switch statement to a jump table."

  case class CaseOutsideSwitch(c: SwitchCase[_]) extends UserError {
    override def code: String = "case"
    override def text: String =
      c.o.messageInContext("This case occurs outside a switch statement.")
  }
  case class BreakWithLabelsNotSupported() extends SystemError {
    override def text: String =
      "Break statements with labels are not yet supported. They should be rewritten to Break statements without labels."
  }

}

case class SwitchToGoto[Pre <: Generation]() extends Rewriter[Pre] {
  val currentCases
      : ScopedStack[ArrayBuffer[(SwitchCase[Pre], LabelDecl[Post])]] = {
    ScopedStack()
  }
  val currentPastSwitchLabel: ScopedStack[Option[LabelDecl[Post]]] = ScopedStack()

  override def dispatch(stat: Statement[Pre]): Statement[Post] =
    stat match {
      case Switch(expr, body) =>
        implicit val o: Origin = stat.o
        val collectedCases = ArrayBuffer[(SwitchCase[Pre], LabelDecl[Post])]()
        val pastSwitch = new LabelDecl[Post]()(o.withContent(PreferredName(Seq(s"past_switch"))))
        val rewrittenBody =
          currentCases.having(collectedCases) {
            currentPastSwitchLabel.having(Some(pastSwitch)) { dispatch(body) }
          }

        val switchValueVariable = new Variable[Post](dispatch(expr.t))
        val switchValue = switchValueVariable.get

        val normalCaseIfs = Block(
          collectedCases.collect { case (c: Case[Pre], label) =>
            Branch(
              Seq((switchValue === dispatch(c.pattern), Goto[Post](label.ref)))
            )
          }.toSeq
        )


        val (newBody, defaultLabel) = collectedCases.collectFirst {
          case (c: DefaultCase[Pre], label) => (rewrittenBody, label)
        }.getOrElse {
          (rewrittenBody, pastSwitch)
        }

        Block(Seq(Scope(
          Seq(switchValueVariable),
          Block(Seq(
            assignLocal(switchValue, dispatch(expr)),
            normalCaseIfs,
            Goto(defaultLabel.ref),
            newBody,
            Label(pastSwitch, Block(Nil))
          )),
        ),

        ))

      case c: SwitchCase[Pre] =>
        currentCases.topOption match {
          case None => throw CaseOutsideSwitch(c)
          case Some(buf) =>
            implicit val o: Origin = c.o
            val replacementLabel = new LabelDecl[Post]()(o.withContent(PreferredName(Seq(c.toString.replace(' ', '_').filterNot(c => c.isWhitespace || c == ':' )))))
            buf += ((c, replacementLabel))
            Label(replacementLabel, Block(Nil))
        }
      case Loop(_,_,_,_,_) =>
        currentPastSwitchLabel.having(None){
        stat.rewriteDefault()
      }
      case Break(None) if currentPastSwitchLabel.top.isEmpty =>
        // break inside a loop => will get rewritten to SIFBreak
        stat.rewriteDefault()
      case Break(None) =>
        // break out of the switch
        Goto[Post](currentPastSwitchLabel.top.get.ref)(stat.o)
      case Break(_) => throw BreakWithLabelsNotSupported()
      case other => rewriteDefault(other)
    }
}
