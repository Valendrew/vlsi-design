(set-logic LIA)
(declare-fun coord_x0 () Int)
(declare-fun coord_x1 () Int)
(declare-fun coord_x2 () Int)
(declare-fun coord_x3 () Int)
(declare-fun coord_x4 () Int)
(declare-fun coord_x5 () Int)
(declare-fun coord_x6 () Int)
(declare-fun coord_x7 () Int)
(declare-fun coord_x8 () Int)
(declare-fun coord_x9 () Int)
(declare-fun coord_y0 () Int)
(declare-fun coord_y1 () Int)
(declare-fun coord_y2 () Int)
(declare-fun coord_y3 () Int)
(declare-fun coord_y4 () Int)
(declare-fun coord_y5 () Int)
(declare-fun coord_y6 () Int)
(declare-fun coord_y7 () Int)
(declare-fun coord_y8 () Int)
(declare-fun coord_y9 () Int)
(declare-fun l () Int)
(assert (and (>= coord_x0 0) (<= coord_x0 13)))
(assert (and (>= coord_x1 0) (<= coord_x1 13)))
(assert (and (>= coord_x2 0) (<= coord_x2 13)))
(assert (and (>= coord_x3 0) (<= coord_x3 13)))
(assert (and (>= coord_x4 0) (<= coord_x4 13)))
(assert (and (>= coord_x5 0) (<= coord_x5 13)))
(assert (and (>= coord_x6 0) (<= coord_x6 13)))
(assert (and (>= coord_x7 0) (<= coord_x7 13)))
(assert (and (>= coord_x8 0) (<= coord_x8 13)))
(assert (and (>= coord_x9 0) (<= coord_x9 13)))
(assert (and (>= coord_y0 0) (<= coord_y0 68)))
(assert (and (>= coord_y1 0) (<= coord_y1 68)))
(assert (and (>= coord_y2 0) (<= coord_y2 68)))
(assert (and (>= coord_y3 0) (<= coord_y3 68)))
(assert (and (>= coord_y4 0) (<= coord_y4 68)))
(assert (and (>= coord_y5 0) (<= coord_y5 68)))
(assert (and (>= coord_y6 0) (<= coord_y6 68)))
(assert (and (>= coord_y7 0) (<= coord_y7 68)))
(assert (and (>= coord_y8 0) (<= coord_y8 68)))
(assert (and (>= coord_y9 0) (<= coord_y9 68)))
(assert (and (>= l 16) (<= l 71)))
(assert (or (<= (+ coord_x0 3) coord_x1) (<= (+ coord_y0 3) coord_y1) (>= (- coord_x0 3) coord_x1) (>= (- coord_y0 4) coord_y1)))
(assert (or (<= (+ coord_x0 3) coord_x2) (<= (+ coord_y0 3) coord_y2) (>= (- coord_x0 3) coord_x2) (>= (- coord_y0 5) coord_y2)))
(assert (or (<= (+ coord_x0 3) coord_x3) (<= (+ coord_y0 3) coord_y3) (>= (- coord_x0 3) coord_x3) (>= (- coord_y0 6) coord_y3)))
(assert (or (<= (+ coord_x0 3) coord_x4) (<= (+ coord_y0 3) coord_y4) (>= (- coord_x0 3) coord_x4) (>= (- coord_y0 7) coord_y4)))
(assert (or (<= (+ coord_x0 3) coord_x5) (<= (+ coord_y0 3) coord_y5) (>= (- coord_x0 3) coord_x5) (>= (- coord_y0 8) coord_y5)))
(assert (or (<= (+ coord_x0 3) coord_x6) (<= (+ coord_y0 3) coord_y6) (>= (- coord_x0 3) coord_x6) (>= (- coord_y0 10) coord_y6)))
(assert (or (<= (+ coord_x0 3) coord_x7) (<= (+ coord_y0 3) coord_y7) (>= (- coord_x0 3) coord_x7) (>= (- coord_y0 12) coord_y7)))
(assert (or (<= (+ coord_x0 3) coord_x8) (<= (+ coord_y0 3) coord_y8) (>= (- coord_x0 4) coord_x8) (>= (- coord_y0 7) coord_y8)))
(assert (or (<= (+ coord_x0 3) coord_x9) (<= (+ coord_y0 3) coord_y9) (>= (- coord_x0 7) coord_x9) (>= (- coord_y0 9) coord_y9)))
(assert (or (<= (+ coord_x1 3) coord_x2) (<= (+ coord_y1 4) coord_y2) (>= (- coord_x1 3) coord_x2) (>= (- coord_y1 5) coord_y2)))
(assert (or (<= (+ coord_x1 3) coord_x3) (<= (+ coord_y1 4) coord_y3) (>= (- coord_x1 3) coord_x3) (>= (- coord_y1 6) coord_y3)))
(assert (or (<= (+ coord_x1 3) coord_x4) (<= (+ coord_y1 4) coord_y4) (>= (- coord_x1 3) coord_x4) (>= (- coord_y1 7) coord_y4)))
(assert (or (<= (+ coord_x1 3) coord_x5) (<= (+ coord_y1 4) coord_y5) (>= (- coord_x1 3) coord_x5) (>= (- coord_y1 8) coord_y5)))
(assert (or (<= (+ coord_x1 3) coord_x6) (<= (+ coord_y1 4) coord_y6) (>= (- coord_x1 3) coord_x6) (>= (- coord_y1 10) coord_y6)))
(assert (or (<= (+ coord_x1 3) coord_x7) (<= (+ coord_y1 4) coord_y7) (>= (- coord_x1 3) coord_x7) (>= (- coord_y1 12) coord_y7)))
(assert (or (<= (+ coord_x1 3) coord_x8) (<= (+ coord_y1 4) coord_y8) (>= (- coord_x1 4) coord_x8) (>= (- coord_y1 7) coord_y8)))
(assert (or (<= (+ coord_x1 3) coord_x9) (<= (+ coord_y1 4) coord_y9) (>= (- coord_x1 7) coord_x9) (>= (- coord_y1 9) coord_y9)))
(assert (or (<= (+ coord_x2 3) coord_x3) (<= (+ coord_y2 5) coord_y3) (>= (- coord_x2 3) coord_x3) (>= (- coord_y2 6) coord_y3)))
(assert (or (<= (+ coord_x2 3) coord_x4) (<= (+ coord_y2 5) coord_y4) (>= (- coord_x2 3) coord_x4) (>= (- coord_y2 7) coord_y4)))
(assert (or (<= (+ coord_x2 3) coord_x5) (<= (+ coord_y2 5) coord_y5) (>= (- coord_x2 3) coord_x5) (>= (- coord_y2 8) coord_y5)))
(assert (or (<= (+ coord_x2 3) coord_x6) (<= (+ coord_y2 5) coord_y6) (>= (- coord_x2 3) coord_x6) (>= (- coord_y2 10) coord_y6)))
(assert (or (<= (+ coord_x2 3) coord_x7) (<= (+ coord_y2 5) coord_y7) (>= (- coord_x2 3) coord_x7) (>= (- coord_y2 12) coord_y7)))
(assert (or (<= (+ coord_x2 3) coord_x8) (<= (+ coord_y2 5) coord_y8) (>= (- coord_x2 4) coord_x8) (>= (- coord_y2 7) coord_y8)))
(assert (or (<= (+ coord_x2 3) coord_x9) (<= (+ coord_y2 5) coord_y9) (>= (- coord_x2 7) coord_x9) (>= (- coord_y2 9) coord_y9)))
(assert (or (<= (+ coord_x3 3) coord_x4) (<= (+ coord_y3 6) coord_y4) (>= (- coord_x3 3) coord_x4) (>= (- coord_y3 7) coord_y4)))
(assert (or (<= (+ coord_x3 3) coord_x5) (<= (+ coord_y3 6) coord_y5) (>= (- coord_x3 3) coord_x5) (>= (- coord_y3 8) coord_y5)))
(assert (or (<= (+ coord_x3 3) coord_x6) (<= (+ coord_y3 6) coord_y6) (>= (- coord_x3 3) coord_x6) (>= (- coord_y3 10) coord_y6)))
(assert (or (<= (+ coord_x3 3) coord_x7) (<= (+ coord_y3 6) coord_y7) (>= (- coord_x3 3) coord_x7) (>= (- coord_y3 12) coord_y7)))
(assert (or (<= (+ coord_x3 3) coord_x8) (<= (+ coord_y3 6) coord_y8) (>= (- coord_x3 4) coord_x8) (>= (- coord_y3 7) coord_y8)))
(assert (or (<= (+ coord_x3 3) coord_x9) (<= (+ coord_y3 6) coord_y9) (>= (- coord_x3 7) coord_x9) (>= (- coord_y3 9) coord_y9)))
(assert (or (<= (+ coord_x4 3) coord_x5) (<= (+ coord_y4 7) coord_y5) (>= (- coord_x4 3) coord_x5) (>= (- coord_y4 8) coord_y5)))
(assert (or (<= (+ coord_x4 3) coord_x6) (<= (+ coord_y4 7) coord_y6) (>= (- coord_x4 3) coord_x6) (>= (- coord_y4 10) coord_y6)))
(assert (or (<= (+ coord_x4 3) coord_x7) (<= (+ coord_y4 7) coord_y7) (>= (- coord_x4 3) coord_x7) (>= (- coord_y4 12) coord_y7)))
(assert (or (<= (+ coord_x4 3) coord_x8) (<= (+ coord_y4 7) coord_y8) (>= (- coord_x4 4) coord_x8) (>= (- coord_y4 7) coord_y8)))
(assert (or (<= (+ coord_x4 3) coord_x9) (<= (+ coord_y4 7) coord_y9) (>= (- coord_x4 7) coord_x9) (>= (- coord_y4 9) coord_y9)))
(assert (or (<= (+ coord_x5 3) coord_x6) (<= (+ coord_y5 8) coord_y6) (>= (- coord_x5 3) coord_x6) (>= (- coord_y5 10) coord_y6)))
(assert (or (<= (+ coord_x5 3) coord_x7) (<= (+ coord_y5 8) coord_y7) (>= (- coord_x5 3) coord_x7) (>= (- coord_y5 12) coord_y7)))
(assert (or (<= (+ coord_x5 3) coord_x8) (<= (+ coord_y5 8) coord_y8) (>= (- coord_x5 4) coord_x8) (>= (- coord_y5 7) coord_y8)))
(assert (or (<= (+ coord_x5 3) coord_x9) (<= (+ coord_y5 8) coord_y9) (>= (- coord_x5 7) coord_x9) (>= (- coord_y5 9) coord_y9)))
(assert (or (<= (+ coord_x6 3) coord_x7) (<= (+ coord_y6 10) coord_y7) (>= (- coord_x6 3) coord_x7) (>= (- coord_y6 12) coord_y7)))
(assert (or (<= (+ coord_x6 3) coord_x8) (<= (+ coord_y6 10) coord_y8) (>= (- coord_x6 4) coord_x8) (>= (- coord_y6 7) coord_y8)))
(assert (or (<= (+ coord_x6 3) coord_x9) (<= (+ coord_y6 10) coord_y9) (>= (- coord_x6 7) coord_x9) (>= (- coord_y6 9) coord_y9)))
(assert (or (<= (+ coord_x7 3) coord_x8) (<= (+ coord_y7 12) coord_y8) (>= (- coord_x7 4) coord_x8) (>= (- coord_y7 7) coord_y8)))
(assert (or (<= (+ coord_x7 3) coord_x9) (<= (+ coord_y7 12) coord_y9) (>= (- coord_x7 7) coord_x9) (>= (- coord_y7 9) coord_y9)))
(assert (or (<= (+ coord_x8 4) coord_x9) (<= (+ coord_y8 7) coord_y9) (>= (- coord_x8 7) coord_x9) (>= (- coord_y8 9) coord_y9)))
(assert (and (<= (+ coord_x0 3) 16) (<= (+ coord_y0 3) l)))
(assert (and (<= (+ coord_x1 3) 16) (<= (+ coord_y1 4) l)))
(assert (and (<= (+ coord_x2 3) 16) (<= (+ coord_y2 5) l)))
(assert (and (<= (+ coord_x3 3) 16) (<= (+ coord_y3 6) l)))
(assert (and (<= (+ coord_x4 3) 16) (<= (+ coord_y4 7) l)))
(assert (and (<= (+ coord_x5 3) 16) (<= (+ coord_y5 8) l)))
(assert (and (<= (+ coord_x6 3) 16) (<= (+ coord_y6 10) l)))
(assert (and (<= (+ coord_x7 3) 16) (<= (+ coord_y7 12) l)))
(assert (and (<= (+ coord_x8 4) 16) (<= (+ coord_y8 7) l)))
(assert (and (<= (+ coord_x9 7) 16) (<= (+ coord_y9 9) l)))
(assert (<= (+ (ite (and (<= coord_y0 3) (< 3 (+ coord_y0 3))) 3 0) (ite (and (<= coord_y1 3) (< 3 (+ coord_y1 4))) 3 0) (ite (and (<= coord_y2 3) (< 3 (+ coord_y2 5))) 3 0) (ite (and (<= coord_y3 3) (< 3 (+ coord_y3 6))) 3 0) (ite (and (<= coord_y4 3) (< 3 (+ coord_y4 7))) 3 0) (ite (and (<= coord_y5 3) (< 3 (+ coord_y5 8))) 3 0) (ite (and (<= coord_y6 3) (< 3 (+ coord_y6 10))) 3 0) (ite (and (<= coord_y7 3) (< 3 (+ coord_y7 12))) 3 0) (ite (and (<= coord_y8 3) (< 3 (+ coord_y8 7))) 4 0) (ite (and (<= coord_y9 3) (< 3 (+ coord_y9 9))) 7 0)) 16))
(assert (<= (+ (ite (and (<= coord_y0 3) (< 3 (+ coord_y0 3))) 3 0) (ite (and (<= coord_y1 3) (< 3 (+ coord_y1 4))) 3 0) (ite (and (<= coord_y2 3) (< 3 (+ coord_y2 5))) 3 0) (ite (and (<= coord_y3 3) (< 3 (+ coord_y3 6))) 3 0) (ite (and (<= coord_y4 3) (< 3 (+ coord_y4 7))) 3 0) (ite (and (<= coord_y5 3) (< 3 (+ coord_y5 8))) 3 0) (ite (and (<= coord_y6 3) (< 3 (+ coord_y6 10))) 3 0) (ite (and (<= coord_y7 3) (< 3 (+ coord_y7 12))) 3 0) (ite (and (<= coord_y8 3) (< 3 (+ coord_y8 7))) 4 0) (ite (and (<= coord_y9 3) (< 3 (+ coord_y9 9))) 7 0)) 16))
(assert (<= (+ (ite (and (<= coord_y0 3) (< 3 (+ coord_y0 3))) 3 0) (ite (and (<= coord_y1 3) (< 3 (+ coord_y1 4))) 3 0) (ite (and (<= coord_y2 3) (< 3 (+ coord_y2 5))) 3 0) (ite (and (<= coord_y3 3) (< 3 (+ coord_y3 6))) 3 0) (ite (and (<= coord_y4 3) (< 3 (+ coord_y4 7))) 3 0) (ite (and (<= coord_y5 3) (< 3 (+ coord_y5 8))) 3 0) (ite (and (<= coord_y6 3) (< 3 (+ coord_y6 10))) 3 0) (ite (and (<= coord_y7 3) (< 3 (+ coord_y7 12))) 3 0) (ite (and (<= coord_y8 3) (< 3 (+ coord_y8 7))) 4 0) (ite (and (<= coord_y9 3) (< 3 (+ coord_y9 9))) 7 0)) 16))
(assert (<= (+ (ite (and (<= coord_y0 3) (< 3 (+ coord_y0 3))) 3 0) (ite (and (<= coord_y1 3) (< 3 (+ coord_y1 4))) 3 0) (ite (and (<= coord_y2 3) (< 3 (+ coord_y2 5))) 3 0) (ite (and (<= coord_y3 3) (< 3 (+ coord_y3 6))) 3 0) (ite (and (<= coord_y4 3) (< 3 (+ coord_y4 7))) 3 0) (ite (and (<= coord_y5 3) (< 3 (+ coord_y5 8))) 3 0) (ite (and (<= coord_y6 3) (< 3 (+ coord_y6 10))) 3 0) (ite (and (<= coord_y7 3) (< 3 (+ coord_y7 12))) 3 0) (ite (and (<= coord_y8 3) (< 3 (+ coord_y8 7))) 4 0) (ite (and (<= coord_y9 3) (< 3 (+ coord_y9 9))) 7 0)) 16))
(assert (<= (+ (ite (and (<= coord_y0 3) (< 3 (+ coord_y0 3))) 3 0) (ite (and (<= coord_y1 3) (< 3 (+ coord_y1 4))) 3 0) (ite (and (<= coord_y2 3) (< 3 (+ coord_y2 5))) 3 0) (ite (and (<= coord_y3 3) (< 3 (+ coord_y3 6))) 3 0) (ite (and (<= coord_y4 3) (< 3 (+ coord_y4 7))) 3 0) (ite (and (<= coord_y5 3) (< 3 (+ coord_y5 8))) 3 0) (ite (and (<= coord_y6 3) (< 3 (+ coord_y6 10))) 3 0) (ite (and (<= coord_y7 3) (< 3 (+ coord_y7 12))) 3 0) (ite (and (<= coord_y8 3) (< 3 (+ coord_y8 7))) 4 0) (ite (and (<= coord_y9 3) (< 3 (+ coord_y9 9))) 7 0)) 16))
(assert (<= (+ (ite (and (<= coord_y0 3) (< 3 (+ coord_y0 3))) 3 0) (ite (and (<= coord_y1 3) (< 3 (+ coord_y1 4))) 3 0) (ite (and (<= coord_y2 3) (< 3 (+ coord_y2 5))) 3 0) (ite (and (<= coord_y3 3) (< 3 (+ coord_y3 6))) 3 0) (ite (and (<= coord_y4 3) (< 3 (+ coord_y4 7))) 3 0) (ite (and (<= coord_y5 3) (< 3 (+ coord_y5 8))) 3 0) (ite (and (<= coord_y6 3) (< 3 (+ coord_y6 10))) 3 0) (ite (and (<= coord_y7 3) (< 3 (+ coord_y7 12))) 3 0) (ite (and (<= coord_y8 3) (< 3 (+ coord_y8 7))) 4 0) (ite (and (<= coord_y9 3) (< 3 (+ coord_y9 9))) 7 0)) 16))
(assert (<= (+ (ite (and (<= coord_y0 3) (< 3 (+ coord_y0 3))) 3 0) (ite (and (<= coord_y1 3) (< 3 (+ coord_y1 4))) 3 0) (ite (and (<= coord_y2 3) (< 3 (+ coord_y2 5))) 3 0) (ite (and (<= coord_y3 3) (< 3 (+ coord_y3 6))) 3 0) (ite (and (<= coord_y4 3) (< 3 (+ coord_y4 7))) 3 0) (ite (and (<= coord_y5 3) (< 3 (+ coord_y5 8))) 3 0) (ite (and (<= coord_y6 3) (< 3 (+ coord_y6 10))) 3 0) (ite (and (<= coord_y7 3) (< 3 (+ coord_y7 12))) 3 0) (ite (and (<= coord_y8 3) (< 3 (+ coord_y8 7))) 4 0) (ite (and (<= coord_y9 3) (< 3 (+ coord_y9 9))) 7 0)) 16))
(assert (<= (+ (ite (and (<= coord_y0 3) (< 3 (+ coord_y0 3))) 3 0) (ite (and (<= coord_y1 3) (< 3 (+ coord_y1 4))) 3 0) (ite (and (<= coord_y2 3) (< 3 (+ coord_y2 5))) 3 0) (ite (and (<= coord_y3 3) (< 3 (+ coord_y3 6))) 3 0) (ite (and (<= coord_y4 3) (< 3 (+ coord_y4 7))) 3 0) (ite (and (<= coord_y5 3) (< 3 (+ coord_y5 8))) 3 0) (ite (and (<= coord_y6 3) (< 3 (+ coord_y6 10))) 3 0) (ite (and (<= coord_y7 3) (< 3 (+ coord_y7 12))) 3 0) (ite (and (<= coord_y8 3) (< 3 (+ coord_y8 7))) 4 0) (ite (and (<= coord_y9 3) (< 3 (+ coord_y9 9))) 7 0)) 16))
(assert (<= (+ (ite (and (<= coord_y0 4) (< 4 (+ coord_y0 3))) 3 0) (ite (and (<= coord_y1 4) (< 4 (+ coord_y1 4))) 3 0) (ite (and (<= coord_y2 4) (< 4 (+ coord_y2 5))) 3 0) (ite (and (<= coord_y3 4) (< 4 (+ coord_y3 6))) 3 0) (ite (and (<= coord_y4 4) (< 4 (+ coord_y4 7))) 3 0) (ite (and (<= coord_y5 4) (< 4 (+ coord_y5 8))) 3 0) (ite (and (<= coord_y6 4) (< 4 (+ coord_y6 10))) 3 0) (ite (and (<= coord_y7 4) (< 4 (+ coord_y7 12))) 3 0) (ite (and (<= coord_y8 4) (< 4 (+ coord_y8 7))) 4 0) (ite (and (<= coord_y9 4) (< 4 (+ coord_y9 9))) 7 0)) 16))
(assert (<= (+ (ite (and (<= coord_y0 7) (< 7 (+ coord_y0 3))) 3 0) (ite (and (<= coord_y1 7) (< 7 (+ coord_y1 4))) 3 0) (ite (and (<= coord_y2 7) (< 7 (+ coord_y2 5))) 3 0) (ite (and (<= coord_y3 7) (< 7 (+ coord_y3 6))) 3 0) (ite (and (<= coord_y4 7) (< 7 (+ coord_y4 7))) 3 0) (ite (and (<= coord_y5 7) (< 7 (+ coord_y5 8))) 3 0) (ite (and (<= coord_y6 7) (< 7 (+ coord_y6 10))) 3 0) (ite (and (<= coord_y7 7) (< 7 (+ coord_y7 12))) 3 0) (ite (and (<= coord_y8 7) (< 7 (+ coord_y8 7))) 4 0) (ite (and (<= coord_y9 7) (< 7 (+ coord_y9 9))) 7 0)) 16))
(assert (<= (+ (ite (and (<= coord_x0 3) (< 3 (+ coord_x0 3))) 3 0) (ite (and (<= coord_x1 3) (< 3 (+ coord_x1 3))) 4 0) (ite (and (<= coord_x2 3) (< 3 (+ coord_x2 3))) 5 0) (ite (and (<= coord_x3 3) (< 3 (+ coord_x3 3))) 6 0) (ite (and (<= coord_x4 3) (< 3 (+ coord_x4 3))) 7 0) (ite (and (<= coord_x5 3) (< 3 (+ coord_x5 3))) 8 0) (ite (and (<= coord_x6 3) (< 3 (+ coord_x6 3))) 10 0) (ite (and (<= coord_x7 3) (< 3 (+ coord_x7 3))) 12 0) (ite (and (<= coord_x8 3) (< 3 (+ coord_x8 4))) 7 0) (ite (and (<= coord_x9 3) (< 3 (+ coord_x9 7))) 9 0)) l))
(assert (<= (+ (ite (and (<= coord_x0 4) (< 4 (+ coord_x0 3))) 3 0) (ite (and (<= coord_x1 4) (< 4 (+ coord_x1 3))) 4 0) (ite (and (<= coord_x2 4) (< 4 (+ coord_x2 3))) 5 0) (ite (and (<= coord_x3 4) (< 4 (+ coord_x3 3))) 6 0) (ite (and (<= coord_x4 4) (< 4 (+ coord_x4 3))) 7 0) (ite (and (<= coord_x5 4) (< 4 (+ coord_x5 3))) 8 0) (ite (and (<= coord_x6 4) (< 4 (+ coord_x6 3))) 10 0) (ite (and (<= coord_x7 4) (< 4 (+ coord_x7 3))) 12 0) (ite (and (<= coord_x8 4) (< 4 (+ coord_x8 4))) 7 0) (ite (and (<= coord_x9 4) (< 4 (+ coord_x9 7))) 9 0)) l))
(assert (<= (+ (ite (and (<= coord_x0 5) (< 5 (+ coord_x0 3))) 3 0) (ite (and (<= coord_x1 5) (< 5 (+ coord_x1 3))) 4 0) (ite (and (<= coord_x2 5) (< 5 (+ coord_x2 3))) 5 0) (ite (and (<= coord_x3 5) (< 5 (+ coord_x3 3))) 6 0) (ite (and (<= coord_x4 5) (< 5 (+ coord_x4 3))) 7 0) (ite (and (<= coord_x5 5) (< 5 (+ coord_x5 3))) 8 0) (ite (and (<= coord_x6 5) (< 5 (+ coord_x6 3))) 10 0) (ite (and (<= coord_x7 5) (< 5 (+ coord_x7 3))) 12 0) (ite (and (<= coord_x8 5) (< 5 (+ coord_x8 4))) 7 0) (ite (and (<= coord_x9 5) (< 5 (+ coord_x9 7))) 9 0)) l))
(assert (<= (+ (ite (and (<= coord_x0 6) (< 6 (+ coord_x0 3))) 3 0) (ite (and (<= coord_x1 6) (< 6 (+ coord_x1 3))) 4 0) (ite (and (<= coord_x2 6) (< 6 (+ coord_x2 3))) 5 0) (ite (and (<= coord_x3 6) (< 6 (+ coord_x3 3))) 6 0) (ite (and (<= coord_x4 6) (< 6 (+ coord_x4 3))) 7 0) (ite (and (<= coord_x5 6) (< 6 (+ coord_x5 3))) 8 0) (ite (and (<= coord_x6 6) (< 6 (+ coord_x6 3))) 10 0) (ite (and (<= coord_x7 6) (< 6 (+ coord_x7 3))) 12 0) (ite (and (<= coord_x8 6) (< 6 (+ coord_x8 4))) 7 0) (ite (and (<= coord_x9 6) (< 6 (+ coord_x9 7))) 9 0)) l))
(assert (<= (+ (ite (and (<= coord_x0 7) (< 7 (+ coord_x0 3))) 3 0) (ite (and (<= coord_x1 7) (< 7 (+ coord_x1 3))) 4 0) (ite (and (<= coord_x2 7) (< 7 (+ coord_x2 3))) 5 0) (ite (and (<= coord_x3 7) (< 7 (+ coord_x3 3))) 6 0) (ite (and (<= coord_x4 7) (< 7 (+ coord_x4 3))) 7 0) (ite (and (<= coord_x5 7) (< 7 (+ coord_x5 3))) 8 0) (ite (and (<= coord_x6 7) (< 7 (+ coord_x6 3))) 10 0) (ite (and (<= coord_x7 7) (< 7 (+ coord_x7 3))) 12 0) (ite (and (<= coord_x8 7) (< 7 (+ coord_x8 4))) 7 0) (ite (and (<= coord_x9 7) (< 7 (+ coord_x9 7))) 9 0)) l))
(assert (<= (+ (ite (and (<= coord_x0 8) (< 8 (+ coord_x0 3))) 3 0) (ite (and (<= coord_x1 8) (< 8 (+ coord_x1 3))) 4 0) (ite (and (<= coord_x2 8) (< 8 (+ coord_x2 3))) 5 0) (ite (and (<= coord_x3 8) (< 8 (+ coord_x3 3))) 6 0) (ite (and (<= coord_x4 8) (< 8 (+ coord_x4 3))) 7 0) (ite (and (<= coord_x5 8) (< 8 (+ coord_x5 3))) 8 0) (ite (and (<= coord_x6 8) (< 8 (+ coord_x6 3))) 10 0) (ite (and (<= coord_x7 8) (< 8 (+ coord_x7 3))) 12 0) (ite (and (<= coord_x8 8) (< 8 (+ coord_x8 4))) 7 0) (ite (and (<= coord_x9 8) (< 8 (+ coord_x9 7))) 9 0)) l))
(assert (<= (+ (ite (and (<= coord_x0 10) (< 10 (+ coord_x0 3))) 3 0) (ite (and (<= coord_x1 10) (< 10 (+ coord_x1 3))) 4 0) (ite (and (<= coord_x2 10) (< 10 (+ coord_x2 3))) 5 0) (ite (and (<= coord_x3 10) (< 10 (+ coord_x3 3))) 6 0) (ite (and (<= coord_x4 10) (< 10 (+ coord_x4 3))) 7 0) (ite (and (<= coord_x5 10) (< 10 (+ coord_x5 3))) 8 0) (ite (and (<= coord_x6 10) (< 10 (+ coord_x6 3))) 10 0) (ite (and (<= coord_x7 10) (< 10 (+ coord_x7 3))) 12 0) (ite (and (<= coord_x8 10) (< 10 (+ coord_x8 4))) 7 0) (ite (and (<= coord_x9 10) (< 10 (+ coord_x9 7))) 9 0)) l))
(assert (<= (+ (ite (and (<= coord_x0 12) (< 12 (+ coord_x0 3))) 3 0) (ite (and (<= coord_x1 12) (< 12 (+ coord_x1 3))) 4 0) (ite (and (<= coord_x2 12) (< 12 (+ coord_x2 3))) 5 0) (ite (and (<= coord_x3 12) (< 12 (+ coord_x3 3))) 6 0) (ite (and (<= coord_x4 12) (< 12 (+ coord_x4 3))) 7 0) (ite (and (<= coord_x5 12) (< 12 (+ coord_x5 3))) 8 0) (ite (and (<= coord_x6 12) (< 12 (+ coord_x6 3))) 10 0) (ite (and (<= coord_x7 12) (< 12 (+ coord_x7 3))) 12 0) (ite (and (<= coord_x8 12) (< 12 (+ coord_x8 4))) 7 0) (ite (and (<= coord_x9 12) (< 12 (+ coord_x9 7))) 9 0)) l))
(assert (<= (+ (ite (and (<= coord_x0 7) (< 7 (+ coord_x0 3))) 3 0) (ite (and (<= coord_x1 7) (< 7 (+ coord_x1 3))) 4 0) (ite (and (<= coord_x2 7) (< 7 (+ coord_x2 3))) 5 0) (ite (and (<= coord_x3 7) (< 7 (+ coord_x3 3))) 6 0) (ite (and (<= coord_x4 7) (< 7 (+ coord_x4 3))) 7 0) (ite (and (<= coord_x5 7) (< 7 (+ coord_x5 3))) 8 0) (ite (and (<= coord_x6 7) (< 7 (+ coord_x6 3))) 10 0) (ite (and (<= coord_x7 7) (< 7 (+ coord_x7 3))) 12 0) (ite (and (<= coord_x8 7) (< 7 (+ coord_x8 4))) 7 0) (ite (and (<= coord_x9 7) (< 7 (+ coord_x9 7))) 9 0)) l))
(assert (<= (+ (ite (and (<= coord_x0 9) (< 9 (+ coord_x0 3))) 3 0) (ite (and (<= coord_x1 9) (< 9 (+ coord_x1 3))) 4 0) (ite (and (<= coord_x2 9) (< 9 (+ coord_x2 3))) 5 0) (ite (and (<= coord_x3 9) (< 9 (+ coord_x3 3))) 6 0) (ite (and (<= coord_x4 9) (< 9 (+ coord_x4 3))) 7 0) (ite (and (<= coord_x5 9) (< 9 (+ coord_x5 3))) 8 0) (ite (and (<= coord_x6 9) (< 9 (+ coord_x6 3))) 10 0) (ite (and (<= coord_x7 9) (< 9 (+ coord_x7 3))) 12 0) (ite (and (<= coord_x8 9) (< 9 (+ coord_x8 4))) 7 0) (ite (and (<= coord_x9 9) (< 9 (+ coord_x9 7))) 9 0)) l))
(assert (ite (and (= 3 3) (= 3 4)) (<= coord_x0 coord_x1) true))
(assert (ite (and (= 3 3) (= 3 5)) (<= coord_x0 coord_x2) true))
(assert (ite (and (= 3 3) (= 3 6)) (<= coord_x0 coord_x3) true))
(assert (ite (and (= 3 3) (= 3 7)) (<= coord_x0 coord_x4) true))
(assert (ite (and (= 3 3) (= 3 8)) (<= coord_x0 coord_x5) true))
(assert (ite (and (= 3 3) (= 3 10)) (<= coord_x0 coord_x6) true))
(assert (ite (and (= 3 3) (= 3 12)) (<= coord_x0 coord_x7) true))
(assert (ite (and (= 3 4) (= 3 7)) (<= coord_x0 coord_x8) true))
(assert (ite (and (= 3 7) (= 3 9)) (<= coord_x0 coord_x9) true))
(assert (ite (and (= 3 3) (= 4 5)) (<= coord_x1 coord_x2) true))
(assert (ite (and (= 3 3) (= 4 6)) (<= coord_x1 coord_x3) true))
(assert (ite (and (= 3 3) (= 4 7)) (<= coord_x1 coord_x4) true))
(assert (ite (and (= 3 3) (= 4 8)) (<= coord_x1 coord_x5) true))
(assert (ite (and (= 3 3) (= 4 10)) (<= coord_x1 coord_x6) true))
(assert (ite (and (= 3 3) (= 4 12)) (<= coord_x1 coord_x7) true))
(assert (ite (and (= 3 4) (= 4 7)) (<= coord_x1 coord_x8) true))
(assert (ite (and (= 3 7) (= 4 9)) (<= coord_x1 coord_x9) true))
(assert (ite (and (= 3 3) (= 5 6)) (<= coord_x2 coord_x3) true))
(assert (ite (and (= 3 3) (= 5 7)) (<= coord_x2 coord_x4) true))
(assert (ite (and (= 3 3) (= 5 8)) (<= coord_x2 coord_x5) true))
(assert (ite (and (= 3 3) (= 5 10)) (<= coord_x2 coord_x6) true))
(assert (ite (and (= 3 3) (= 5 12)) (<= coord_x2 coord_x7) true))
(assert (ite (and (= 3 4) (= 5 7)) (<= coord_x2 coord_x8) true))
(assert (ite (and (= 3 7) (= 5 9)) (<= coord_x2 coord_x9) true))
(assert (ite (and (= 3 3) (= 6 7)) (<= coord_x3 coord_x4) true))
(assert (ite (and (= 3 3) (= 6 8)) (<= coord_x3 coord_x5) true))
(assert (ite (and (= 3 3) (= 6 10)) (<= coord_x3 coord_x6) true))
(assert (ite (and (= 3 3) (= 6 12)) (<= coord_x3 coord_x7) true))
(assert (ite (and (= 3 4) (= 6 7)) (<= coord_x3 coord_x8) true))
(assert (ite (and (= 3 7) (= 6 9)) (<= coord_x3 coord_x9) true))
(assert (ite (and (= 3 3) (= 7 8)) (<= coord_x4 coord_x5) true))
(assert (ite (and (= 3 3) (= 7 10)) (<= coord_x4 coord_x6) true))
(assert (ite (and (= 3 3) (= 7 12)) (<= coord_x4 coord_x7) true))
(assert (ite (and (= 3 4) (= 7 7)) (<= coord_x4 coord_x8) true))
(assert (ite (and (= 3 7) (= 7 9)) (<= coord_x4 coord_x9) true))
(assert (ite (and (= 3 3) (= 8 10)) (<= coord_x5 coord_x6) true))
(assert (ite (and (= 3 3) (= 8 12)) (<= coord_x5 coord_x7) true))
(assert (ite (and (= 3 4) (= 8 7)) (<= coord_x5 coord_x8) true))
(assert (ite (and (= 3 7) (= 8 9)) (<= coord_x5 coord_x9) true))
(assert (ite (and (= 3 3) (= 10 12)) (<= coord_x6 coord_x7) true))
(assert (ite (and (= 3 4) (= 10 7)) (<= coord_x6 coord_x8) true))
(assert (ite (and (= 3 7) (= 10 9)) (<= coord_x6 coord_x9) true))
(assert (ite (and (= 3 4) (= 12 7)) (<= coord_x7 coord_x8) true))
(assert (ite (and (= 3 7) (= 12 9)) (<= coord_x7 coord_x9) true))
(assert (ite (and (= 4 7) (= 7 9)) (<= coord_x8 coord_x9) true))
(assert (= coord_x9 0))
(assert (= coord_y9 0))
(check-sat)
(get-value (coord_x0))
(get-value (coord_y0))
(get-value (coord_x1))
(get-value (coord_y1))
(get-value (coord_x2))
(get-value (coord_y2))
(get-value (coord_x3))
(get-value (coord_y3))
(get-value (coord_x4))
(get-value (coord_y4))
(get-value (coord_x5))
(get-value (coord_y5))
(get-value (coord_x6))
(get-value (coord_y6))
(get-value (coord_x7))
(get-value (coord_y7))
(get-value (coord_x8))
(get-value (coord_y8))
(get-value (coord_x9))
(get-value (coord_y9))
(get-value (l))
