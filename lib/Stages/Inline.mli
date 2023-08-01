open! Base

val inline
  :  ExplicitNucleus.t
  -> (CompilerState.state, InlineNucleus.t, string) CompilerState.t

module Stage (SB : Source.BuilderT) :
  CompilerPipeline.Stage
    with type state = CompilerState.state
    with type input = ExplicitNucleus.t
    with type output = InlineNucleus.t
    with type error = (SB.source option, string) Source.annotate
