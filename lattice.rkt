#lang racket

(provide (struct-out lattice))

(struct lattice (join gte bottom top))
