#lang racket/signature
#;(-> variable symbolic-value)
symbolic-boolean

#;Value 
initial-value

#;(-> (-> state value) (-> state value) (-> state value))
f-or

#;(-> (-> state value) (-> state value) (-> state value))
f-and

#;(-> (-> state value) (-> state value))
f-not

#;(-> (-> state value) (-> state value) (-> state value))
f-implies

#;(-> state symbolic-boolean)
constraints

#;(-> circuit (-> state boolean))
constructive?

#;(-> circuit state)
initialize-to-false

#;(-> circuit state)
initialize-to-true

#;(-> natural natural)
get-maximal-statespace

#;(-> circuit natural)
interp-bound

#;(-> state state boolean)
outputs=?

#;(-> circuit expression)
constructive-constraints