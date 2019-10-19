#lang racket/base
(provide (struct-out circuit))
(struct circuit (outputs inputs reg-pairs term)
  #:transparent)