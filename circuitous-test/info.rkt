#lang info

(define collection 'multi)

(define deps
  '(("base" #:version "7.4")
    "https://github.com/emina/rosette.git#c092b65b8831726487edd1e63b4390508db483d2"
    "circuitous-lib"))


(define build-deps '("rackunit-lib"
                     "redex-lib"
                     "threading-lib"
                     ))

(define pkg-desc "Tests for `circuitous`")

(define version "0.1")
