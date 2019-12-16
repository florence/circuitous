#lang info

(define collection 'multi)

(define deps
  '("redex-lib"
    ("base" #:version "7.4")
    "rosette"))


(define build-deps '("rackunit-lib"
                     ))

(define pkg-desc "Implementation part of `circuitous`")

(define version "0.1")