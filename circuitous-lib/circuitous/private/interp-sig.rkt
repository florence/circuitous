#lang racket/signature

#;(-> circuit circuit
      #:register-pairs1 [(or #f (listof variable variable))]
      #:register-pairs2 [(or #f (listof variable variable))]
      #:constraints [expression]
      #:outputs [(or #f (listof symbol))]
      (or unsat? (list model? state)))
verify-same

#;(-> circuit #:exclude [(listof variable)] (listof (list variable symbolic-variable)))
symbolic-inputs

#;(-> circuit (listof (list variable symbolic-variable)) state)
build-state

#;(-> circuit (listof (list variable (-> state booolean))))
build-formula

#;(-> expression (-> state booolean))
build-expression

#;(-> state circuit-as-functions state)
eval

#;(-> (listof state) circuit-as-functions (listof (list variable variable)) (listof state))
eval/multi

#;(-> (listof state) circuit (listof (list variable variable)) (listof state))
eval/multi*

#;(-> state state #:outputs [(listof variable)] boolean?)
result=?

#;(-> (listof state) (listof state) #:outputs [(listof variable)] boolean?)
result=?/multi

totally-constructive?