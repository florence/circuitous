#lang scribble/manual
@require[(for-label circuitous
                    racket/list
                    racket/contract)]


@author[@[author+email "Spencer Florence" "spencer.florence@eecs.northwestern.edu"]]

@title["Circuitous: a circuit reasoning library"]

@declare-exporting[circuitous]
@defmodule[circuitous]


@section["Data"]

@defproc[(circuit? [it any/c])
         boolean?]{

Is @racket[it] a circuit.

}

@defproc[(constructive-circuit? [c circuit?])
         boolean?]{

 Is @racket[c] represented using constructive logic?
 The values on the wires of @racket[c] are drawn from
 @racket[#f], @racket[#t], and @racket['⊥], and wire names
 are @racket[symbol?]s.

}

@defproc[(classical-circuit? [c circuit?])
         boolean?]{

 Is @racket[c] represented using classical logic?
 The values on the wires of @racket[c] are drawn from
 @racket[#f], @racket[#t]. Wires are divided into pairs,
 names @racket[(+ symbol?)] and @racket[(- symbol?)].
 The positive part is true if the wire carries
 @racket[#t], and the negative part is true if
 the wire carries @racket[#f].

}

@defproc[(same-circuit-as/c [c circuit?])
         contract?]{
 Constructs a contract that matches @racket[constructive-circuit?]
 if @racket[c] is a @racket[constructive-circuit?], and
 @racket[classical-circuit?] if @racket[c] is a
 @racket[classical-circuit?].
}

@defproc[(circuit-inputs [c circuit?])
         (listof variable/c)]{
 Gets all inputs to @racket[c].
}

@defproc[(circuit-domain [c circuit?])
         (listof variable/c)]{
 Gets the names of all wires defined
 in the circuit.
}

@defproc[(circuit-outputs [c circuit?])
         (listof variable/c)]{
 Gets all outputs to @racket[c].
}

@defproc[(circuit-domain [c circuit?])
         (listof variable/c)]{
 Gets the names of all wires defined
 in the circuit.
}

@defproc[(circuit-term [c circuit?])
         (listof (list/c variable/c '= boolean-expression/c))]{

Gets a symbolic representation of the equations that define
the circuit.

}
         
@defthing[variable/c flat-contract?]{
 TODO
}

@defthing[boolean-expression/c flat-contract?]{
 TODO
}

@section["Constructing Circuits"]

@defproc[(make-circuit [#:inputs inputs (listof symbol?)]
                       [#:outputs output (listof symbol?)]
                       [equations
                        (listof (list/c symbol? '= boolean-expression/c))]
                       [#:register-pairs registers
                        (listof (list/c symbol? symbol?))
                        empty])
         constructive-circuit?]{

 Construct a circuit defined by @racket[equations]. The inputs
 to the circuit @racket[inputs] must not be defined by the @racket[equations].
 The is no such constraint on the @racket[outputs]. Any output not defined
 by @racket[equations] is taken to be @racket[#f].
 
}

@defproc[(link [a circuit?]
               [#:with b circuit?]
               [#:inputs inputs (listof variable/c variable/c)]
               [#:outputs outputs (listof variable/c variable/c)])
         (and/c circuit? (same-circuit-as/c a))]{
}

@section["Circuit Equality"]

