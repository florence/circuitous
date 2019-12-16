#lang info

(define collection 'multi)

(define deps
  '(("base" #:version "7.4")
    "rosette"
    "circuitous-lib"))


(define build-deps '("rackunit-lib"
                     "redex-lib"
                     "threading-lib"
                     ))

(define pkg-desc "Tests for `circuitous`")

(define version "0.1")
