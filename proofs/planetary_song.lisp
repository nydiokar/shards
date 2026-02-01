;; Common Lisp proof
(defun frequency (shard)
  (+ 432 (* 432 (/ (1+ shard) 71.0))))

(let* ((min-freq (frequency 0))
       (max-freq (frequency 70))
       (ratio (/ max-freq min-freq)))
  (format t "Min: ~,2f Hz, Max: ~,2f Hz, Ratio: ~,4f~%" min-freq max-freq ratio)
  (assert (< (abs (- ratio 2.0)) 0.05))
  (format t "✓ Lisp: Octave verified [~,2f-~,2f Hz]~%" min-freq max-freq))
