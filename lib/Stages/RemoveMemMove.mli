open! Base

val removeMemMoves
  :  Acorn.withCaptures
  -> (CompilerState.state, Acorn.withCaptures, _) State.t

module Stage (SB : Source.BuilderT) :
  CompilerPipeline.Stage
    with type state = CompilerState.state
    with type input = Acorn.withCaptures
    with type output = Acorn.withCaptures
    with type error = (SB.source option, string) Source.annotate
