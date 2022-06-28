#lang info

(define collection 'multi)

(define deps
  '("redex-lib"
    ("base" #:version "7.4")
    "https://github.com/emina/rosette.git#c092b65b8831726487edd1e63b4390508db483d2"))


(define build-deps '("rackunit-lib"
                     ))

(define pkg-desc "Implementation part of `circuitous`")

(define version "0.1")