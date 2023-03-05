

(define (problem BW-rand-3)
(:domain blocksworld)
(:objects b1 b2 - block)
(:init
(on-table b1)
(clear b2)
(same b1 b1)
(same b2 b2)


(unknown (on b2 b1))
(unknown (on-table b2))
(unknown (clear b1))


(oneof
(on-table b2)
(on b2 b1)
)
(oneof
(clear b1)
(on b2 b1)
)
)
(:goal
(and
(on b1 b2)
)
)
)


