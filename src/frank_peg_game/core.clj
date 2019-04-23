(ns frank-peg-game.core
  (:gen-class)
  (:require [clojure.repl :refer :all]))

;; Objective: To reverse engineer the game by only interacting with the game

;; What is the game?
;; Given a triangle shaped board with rows of holes filled, first pick out a peg in the
;; beginning of the game, then try to remove as many pegs as you can till you can no longer do
;; so. You can remove a peg by jumping a peg over it to an adjacent empty hole.
;; Rules 1: Remove any peg from the board in the beginning
;; Rules 2: Make a valid move by jumping a peg over another one to its adjacent
;; (jumps vertically or horizontally)vacant hole.
;; Rules 3: Game is over when you can no longer make a valid move

;; How to store the state of the game?
(def board-proto
  {:nrows 3,
   :holes {
           1 {:pegged true, :connections {}}
           2 {:pegged true, :connections {}}
           3 {:pegged true, :connections {}}
           4 {:pegged true, :connections {}}
           5 {:pegged true, :connections {}}
           6 {:pegged true, :connections {}}
           },
   })
(def board0
  {:nrows 3,
   :holes {
           1 {:pegged true, :connections {4 2, 6 3}}
           2 {:pegged true, :connections {}}
           3 {:pegged true, :connections {}}
           4 {:pegged true, :connections {1 2, 6 5}}
           5 {:pegged true, :connections {}}
           6 {:pegged true, :connections {1 3, 4 5}}
           },
   })
;; Say we picked "a" to initialize the game
(def board1
  {:nrows 3,
   :holes {
           1 {:pegged false, :connections {4 2, 6 3}}
           2 {:pegged true, :connections {}}
           3 {:pegged true, :connections {}}
           4 {:pegged true, :connections {1 2, 6 5}}
           5 {:pegged true, :connections {}}
           6 {:pegged true, :connections {1 3, 4 5}}
           },
   })

;; Say we do "da"
(def board2
  {:nrows 3,
   :holes {
           ;; Completion State Check:
           ;; Check if game is over, i.e. no valid moves left, for now just iterate over all holes, check for any valid move from each hole

           ;; validation steps:
           ;; convert "da" to another representation, (def movement {:origin 4, :dest 1})
           ;; check if (:dest movement) is pegged b/c it's gotta be empty
           ;; check if (get (:connections (:origin movement)) 1) or if the "jumpee" is pegged
           ;; b/c it's gotta be not empty

           ;; If validation fails, prompt user for another move

           ;; state transition:

           1 {:pegged true, :connections {4 2, 6 3}} ;; 1. changed pegged to true
           2 {:pegged false, :connections {}} ;; 2. changed pegged to true for it just got jumped over
           3 {:pegged true, :connections {}}
           4 {:pegged false, :connections {1 2, 6 5}}
           5 {:pegged true, :connections {}}
           6 {:pegged true, :connections {1 3, 4 5}}
           },
   })

;; ------------------------------------------Design-------------------------------------------

;; 3 categories of functions

;; 1. Creating The Board
;; 2. State Transition
;; 3. Ui and User Interactions

;; Creating the Board:
;; given number of rows, create a board

;; State Sransition:
;; give a move, origin and destination, validate the move and perform state transition

;; UI and User Interactions:
;; 1. Prompt if 1) invalid move 2) game is finished, report score, and if replay?
;; 3) number of rows 4) Visualize board after a state is computed


;; ------------------------------------------Creating the board------------------------------

;; directions to jump, upper & lower left, upper & lower right, left, right
;; e.g. 3 4 5 (left), 1 to 4 (lower left), 1 to 6 (lower right)

(defmacro assert-equal-tell [[_ expr val]]
  `(let [expr-val# ~expr]
     (assert (= expr-val# ~val) (str "\n\nProgram returns:\n" expr-val# "\n\n But correct value is:\n" ~val))))

(defn gen-tri-seq
  ([] (gen-tri-seq 1 0))
  ([nth prev]
   (lazy-seq
    (let [cur (+ nth prev)]
      (cons cur (gen-tri-seq (inc nth) cur))))))

(def tri-seq (gen-tri-seq))

(assert-equal-tell (= (take 5 tri-seq) '(1 3 6 10 15)))

(defn row-num [n]
  "The row num of n on the board."
  (inc (count (take-while #(< % n) tri-seq))))

(assert-equal-tell (= (row-num 2) 2))
(assert-equal-tell (= (row-num 5) 3))
(assert-equal-tell (= (row-num 9) 4))

(defn lower-left-move [n]
  "Given a number on the board, calculate the lower left position if it were to jump in
the lower left direction"
  (let [row-num-n (row-num n)]
    (+ n row-num-n (inc row-num-n))))

(assert-equal-tell (= (lower-left-move 1) 4))
(assert-equal-tell (= (lower-left-move 5) 12))
(assert-equal-tell (= (lower-left-move 3) 8))
(assert-equal-tell (= (lower-left-move 6) 13))

(defn lower-right-move [n]
  (let [row-num-n (row-num n)]
    (+ n (inc row-num-n) (
                          + 2 row-num-n))))

(assert-equal-tell (= (lower-right-move 1) 6))
(assert-equal-tell (= (lower-right-move 5) 14))
(assert-equal-tell (= (lower-right-move 3) 10))
(assert-equal-tell (= (lower-right-move 6) 15))
(assert-equal-tell (= (lower-right-move 4) 13))

(defn lower-left-adjacent [n]
  "Get adjacent number in the lower right direction"
  (+ (row-num n) n))

(assert-equal-tell (= (lower-left-adjacent 1) 2))
(assert-equal-tell (= (lower-left-adjacent 5) 8))
(assert-equal-tell (= (lower-left-adjacent 3) 5))
(assert-equal-tell (= (lower-left-adjacent 6) 9))
(assert-equal-tell (= (lower-left-adjacent 4) 7))

(defn lower-right-adjacent [n]
  "Get adjacent number in the lower right direction"
  (+ (inc (row-num n)) n))

(assert-equal-tell (= (lower-right-adjacent 1) 3))
(assert-equal-tell (= (lower-right-adjacent 5) 9))
(assert-equal-tell (= (lower-right-adjacent 3) 6))
(assert-equal-tell (= (lower-right-adjacent 6) 10))
(assert-equal-tell (= (lower-right-adjacent 4) 8))

(defn max-num [num-rows] (last (take num-rows tri-seq)))

(defn make-diagonal-connections [board origin]
  "make connection for jupming diagonally"
  (let [l-left-move (lower-left-move origin)
        l-right-move (lower-right-move origin)
        l-left-adj (lower-left-adjacent origin)
        l-right-adj (lower-right-adjacent origin)
        board-max-num (max-num (:nrows board))
        origin-conn-key [:holes origin :connections]
        left-move-conn-key [:holes l-left-move :connections]
        right-move-conn-key [:holes l-right-move :connections]]
    (if (<= l-right-move board-max-num)
      (assoc-in
       (assoc-in
        (assoc-in
         board
         origin-conn-key
         (merge
          (get-in board origin-conn-key)
          {l-left-move l-left-adj,
           l-right-move l-right-adj}))
        left-move-conn-key
        (merge
         (get-in board left-move-conn-key)
         {origin l-left-adj}))
       right-move-conn-key
       (merge
        {origin l-right-adj}
        (get-in board right-move-conn-key)))
      board)))

(def test-board-3
  {:nrows 3,
   :holes {
           1 {:pegged true, :connections {}}
           2 {:pegged true, :connections {}}
           3 {:pegged true, :connections {}}
           4 {:pegged true, :connections {}}
           5 {:pegged true, :connections {}}
           6 {:pegged true, :connections {}}
           },
   })

(assert-equal-tell (= (make-diagonal-connections test-board-3 1)
                      {:nrows 3,
                       :holes {
                               1 {:pegged true, :connections {4 2, 6 3}}
                               2 {:pegged true, :connections {}}
                               3 {:pegged true, :connections {}}
                               4 {:pegged true, :connections {1 2}}
                               5 {:pegged true, :connections {}}
                               6 {:pegged true, :connections {1 3}}
                               },
                       }))

(defn make-right-connection [board origin]
  "make connection for jumping left to right"
  (let [origin-row-num (row-num origin)
        last-in-row (nth tri-seq (dec origin-row-num))
        last-in-row? (= origin last-in-row)
        second-last-in-row? (= origin (dec last-in-row))
        horizontal-moves? (and (not last-in-row?) (not second-last-in-row?))
        right-move (+ 2 origin)
        right-adj (inc origin)
        origin-conn-k [:holes origin :connections]
        right-move-conn-k [:holes right-move :connections]]
    (if horizontal-moves?
      (assoc-in
       (assoc-in board
                 origin-conn-k
                 (merge (get-in board origin-conn-k)
                        {right-move right-adj}))
       right-move-conn-k
       (merge (get-in board right-move-conn-k)
              {origin right-adj}))
      board)))


(assert-equal-tell (= (make-right-connection (make-diagonal-connections test-board-3 1) 4)
                      {:nrows 3,
                       :holes {
                               1 {:pegged true, :connections {4 2, 6 3}}
                               2 {:pegged true, :connections {}}
                               3 {:pegged true, :connections {}}
                               4 {:pegged true, :connections {1 2, 6 5}}
                               5 {:pegged true, :connections {}}
                               6 {:pegged true, :connections {1 3, 4 5}}
                               },
                       }))

(assert-equal-tell (= (make-right-connection (make-diagonal-connections test-board-3 1) 5)
                      {:nrows 3,
                       :holes {
                               1 {:pegged true, :connections {4 2, 6 3}}
                               2 {:pegged true, :connections {}}
                               3 {:pegged true, :connections {}}
                               4 {:pegged true, :connections {1 2}}
                               5 {:pegged true, :connections {}}
                               6 {:pegged true, :connections {1 3}}
                               },
                       }))

(defn make-unpegged-board [num-rows]
  {:nrows num-rows
   :holes (loop [i 1 board (sorted-map)]
            (if (> i (max-num num-rows)) board
                (recur
                 (inc i)
                 (assoc
                  board
                  i
                  {:pegged true, :connections {}}))))})

(defn make-board [num-rows]
  (reduce
   (fn [board n] (make-right-connection
                  (make-diagonal-connections board n) n))
   (make-unpegged-board num-rows)
   (take-while #(<= % (max-num num-rows)) (iterate inc 1))))


(assert-equal-tell (= (make-board 3)
                      {:nrows 3,
                       :holes
                       {1 {:pegged true, :connections {4 2, 6 3}},
                        2 {:pegged true, :connections {}},
                        3 {:pegged true, :connections {}},
                        4 {:pegged true, :connections {1 2, 6 5}},
                        5 {:pegged true, :connections {}},
                        6 {:pegged true, :connections {1 3, 4 5}}}}))

(assert-equal-tell (= (make-board 5)
                      {:nrows 5,
                       :holes
                       {1 {:pegged true, :connections {4 2, 6 3}},
                        2 {:pegged true, :connections {7 4, 9 5}},
                        3 {:pegged true, :connections {8 5, 10 6}},
                        4 {:pegged true, :connections {1 2, 11 7, 13 8, 6 5}},
                        5 {:pegged true, :connections {12 8, 14 9}},
                        6 {:pegged true, :connections {1 3, 4 5, 13 9, 15 10}},
                        7 {:pegged true, :connections {2 4, 9 8}},
                        8 {:pegged true, :connections {3 5, 10 9}},
                        9 {:pegged true, :connections {2 5, 7 8}},
                        10 {:pegged true, :connections {3 6, 8 9}},
                        11 {:pegged true, :connections {4 7, 13 12}},
                        12 {:pegged true, :connections {5 8, 14 13}},
                        13 {:pegged true, :connections {4 8, 6 9, 11 12, 15 14}},
                        14 {:pegged true, :connections {5 9, 12 13}},
                        15 {:pegged true, :connections {6 10, 13 14}}}}))

;; ----------------------- State Transition -----------------------------

;; Move validation
;; Given origin, destination
;; 1.check if origin is pegged
;; 2.check if dest in the keys of connections
;; 3.check if the adjacent, that is the hole between dest and origin, is pegged
;; validated

(defn is-pegged? [board n] (get-in board [:holes n :pegged]))
(defn adjacent [board origin dest] (get-in board [:holes origin :connections dest]))
(defn are-connected? [board origin dest] (not (nil? (adjacent board origin dest))))
(defn valid-move? [board origin dest]
  (every? true?
          [(is-pegged? board origin)
           (are-connected? board origin dest)
           (let [adj (adjacent board origin dest)]
             (is-pegged? board adj))]))

(def test-board-3-top-removed
  {:nrows 3,
   :holes
   {1 {:pegged false, :connections {4 2, 6 3}},
    2 {:pegged true, :connections {}},
    3 {:pegged true, :connections {}},
    4 {:pegged true, :connections {1 2, 6 5}},
    5 {:pegged true, :connections {}},
    6 {:pegged true, :connections {1 3, 4 5}}}})

(assert-equal-tell (=
                    (valid-move?
                     test-board-3-top-removed
                     1
                     4)
                    false))

(assert-equal-tell (=
                    (valid-move?
                     test-board-3-top-removed
                     1
                     6)
                    false))

(assert-equal-tell (=
                    (valid-move?
                     test-board-3-top-removed
                     1
                     3)
                    false))

(assert-equal-tell (=
                    (valid-move?
                     test-board-3-top-removed
                     4
                     1)
                    true))

(assert-equal-tell (=
                    (valid-move?
                     test-board-3-top-removed
                     6
                     1)
                    true))

(defn make-move [board origin dest]
  (if (valid-move? board origin dest)
    (let [dest-pegged-key [:holes dest :pegged]
          origin-pegged-key [:holes origin :pegged]
          adj-pegged-key [:holes (adjacent board origin dest) :pegged]]
      (-> board
          (assoc-in origin-pegged-key false)
          (assoc-in adj-pegged-key false)
          (assoc-in dest-pegged-key true)))
    board))

(assert-equal-tell (=
                    (make-move test-board-3-top-removed 4 1)
                    {:nrows 3,
                     :holes
                     {1 {:pegged true, :connections {4 2, 6 3}},
                      2 {:pegged false, :connections {}},
                      3 {:pegged true, :connections {}},
                      4 {:pegged false, :connections {1 2, 6 5}},
                      5 {:pegged true, :connections {}},
                      6 {:pegged true, :connections {1 3, 4 5}}}}))

(assert-equal-tell (=
                    (make-move test-board-3-top-removed 3 1)
                    test-board-3-top-removed))

;; *** When I write code, am I depending too much on the data structure? I.e. too much coupling betwee data and processes ***

(defn valid-move-from-origin? [board origin]
  (let [valid-dests (keys (get-in board [:holes origin :connections]))]
    (not-every? false? (map #(valid-move? board origin %) valid-dests))))

(defn is-game-over? [board]
  (let [origins (keys (get-in board [:holes]))]
    (every? false? (map (partial valid-move-from-origin? board) origins))))

(assert-equal-tell (=
                    (is-game-over? {:nrows 3,
                                    :holes
                                    {1 {:pegged false, :connections {4 2, 6 3}},
                                     2 {:pegged false, :connections {}},
                                     3 {:pegged false, :connections {}},
                                     4 {:pegged true, :connections {1 2, 6 5}},
                                     5 {:pegged false, :connections {}},
                                     6 {:pegged true, :connections {1 3, 4 5}}}})
                    true))

(assert-equal-tell (=
                    (is-game-over? {:nrows 3,
                                    :holes
                                    {1 {:pegged false, :connections {4 2, 6 3}},
                                     2 {:pegged false, :connections {}},
                                     3 {:pegged true, :connections {}},
                                     4 {:pegged false, :connections {1 2, 6 5}},
                                     5 {:pegged true, :connections {}},
                                     6 {:pegged true, :connections {1 3, 4 5}}}})
                    false))

;; --------------------------- Ui and User Interactions-------------------------------------

;; User prompts
(defn get-user-answer [question-txt]
  (println question-txt)
  (read-line))

(defn greeting []
  (println "\nWelcome to Frank's the Peg Game (¬‿¬)"))

(defn get-num-rows []
  (Integer/parseInt (get-user-answer "\nHow many rows?")))

(defn convert-letter [n]
  "1 -> (char) a"
  (let [asicc-pad 96]
    (char (+ asicc-pad n))))

(defn convert-to-number [s]
  (- (int (first s)) 96))

(defn get-first-removal []
  (get-user-answer "\nRemove the first peg"))

;; Visualization

(defn print-row-centered [nth-row num-rows text]
  "text will always be 2 characters long"
  (let [text-len (count text)
        last-row-num-chars (+ (* num-rows 2) (dec num-rows))
        normalized-last-row-nchars (if (even? text-len)
                                     (if (even? last-row-num-chars)
                                       last-row-num-chars
                                       (inc last-row-num-chars))
                                     (if (odd? last-row-num-chars)
                                       last-row-num-chars
                                       (inc last-row-num-chars)))
        space-pad (apply str (take (/ (- normalized-last-row-nchars text-len) 2) (repeat " ")))]
    (printf "%s%s%s\n" space-pad text space-pad)))

(defn row-seq [row-number]
  (if (= row-number 1)
    [1]
    (let [start (inc (nth tri-seq (- row-number 2)))
         end (inc (nth tri-seq (dec row-number)))]
     (range start end))))

(assert-equal-tell (= (into [] (row-seq 3)) [4 5 6]))
(assert-equal-tell (= (into [] (row-seq 1)) [1]))
(assert-equal-tell (= (into [] (row-seq 5)) [11 12 13 14 15]))

(defn print-board [board]
  (let [triangle-seq (map #(row-seq %) (range 1 (inc (:nrows board))))
        letterized-board (map
                          (fn [row]
                            (map #(str (convert-letter %) (if (is-pegged? board %) "@" "-"))
                                 row))
                          triangle-seq)]
    (doseq [row-number (range 1 (inc (count letterized-board)))]
      (print-row-centered row-number
                          (:nrows board)
                          (apply str
                                 (interleave (nth letterized-board (dec row-number))
                                             (repeat " ")))))))

(greeting)
(def board (atom (make-board (get-num-rows))))
(def first-removal (convert-to-number (get-first-removal)))
(swap! board assoc-in [:holes first-removal :pegged] false)
(print-board @board)
(while (not (is-game-over? @board))
  (do (let [move (get-user-answer "Enter your move")
            origin (convert-to-number (str (first move)))
            dest (convert-to-number (str (second move)))]
        (swap! board make-move origin dest))
      (print-board @board)))

;; "f d" breaks everything?
;;  aO       
;; bO cO     
;; d@ eO f@    
;; g@ h@ i@ j@  
;; k@ l@ m@ n@ o@
;; 

;; *** How to write this better? I.e. less bugs and more readable ***
