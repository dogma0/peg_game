(ns frank-peg-game.core
  (:gen-class)
  (:require [clojure.repl :refer :all]
            [clojure.test :refer :all]))

;; ============================== Description of Project and Glossary==========================
;; The game starts with a triangular board with each "hole" "pegged". The one and only player
;; first removes a "peg"" from the board to begin the game. The goal of the game is to leave as
;; few pegs on the board as possible. The proceed in the game, the player can make a "move" by
;; removing a peg at a location (origin) and "jumping" it to a hole (destination) with one peg (adjacent) in between  the "origin" and
;; "destination"; the jump has to be either in the "horizontal" or "diagonal" direction. The score for the game is calculated and the game is finished when the
;; player can no longer make any more jumps.

;; ===================================Calculation for Peg Board==================================

(defn generate-triangular-seq
  "Generate a sequence of triangular numbers."
  ([] (generate-triangular-seq 1 0))
  ([nth prev]
   (lazy-seq
    (let [cur (+ nth prev)]
      (cons cur (generate-triangular-seq (inc nth) cur))))))

(def triangular-seq
  (generate-triangular-seq))

(defn row-num [num]
  "The number for row n is in on the board, 1-based."
  (inc (count (take-while #(< % num) triangular-seq))))

(defn lower-left-move [num]
  "The lower left move's num for num, treating the board as infinitly sized."
  (let [row-num-res (row-num num)]
    (+ num row-num-res (inc row-num-res))))

(defn lower-right-move [num]
  "The lower right move's num for num, treating the board as infinitly sized."
  (let [row-num-res (row-num num)]
    (+ num (inc row-num-res) (+ 2 row-num-res))))

(defn right-move [num] (+ num 2))

(defn right-adj [num] (inc num))

(defn lower-left-adjacent [num]
  "The lower left adjacent space's num for num, treating the board as infinitly sized."
  (+ (row-num num) num))

(defn lower-right-adjacent [num]
  (+ (inc (row-num num)) num))

(defn max-num [nrows]
  "The maximum number that exists on the board."
  (last (take nrows triangular-seq)))

(defn conn-key [num] [:holes num :connections])

(defn connections [board num]
  "Connections originated from num."
  (get-in board (conn-key num)))

(defn in-between [board origin dest] (get (connections board origin) dest))

(defn is-pegged? [board num]
  (get-in board [:holes num :pegged]))

(defn nrows [board]
  "The number of rows on the board."
  (:nrows board))

(defn update-conns [board num next-conns]
  "New board with next-conns replaced for num's connections."
  (assoc-in board (conn-key num) next-conns))

(defn add-conns [board num new-conns]
  "Taking in new connections and essentially append to num's connections."
  (update-conns board num (merge (connections board num) new-conns)))

(defn origin-dia-connected-board [board origin]
  "Board with origin's diagonal connections made."
  (add-conns board origin {(lower-left-move origin) (lower-left-adjacent origin),
                           (lower-right-move origin) (lower-right-adjacent origin)}))

(defn lower-left-connected-board [board origin]
  "Board with the connections of the lower left move of origin made."
  (add-conns board (lower-left-move origin) {origin (lower-left-adjacent origin)}))

(defn lower-right-connected-board [board origin]
  "Board with the connections of the lower right move of origin made."
  (add-conns board (lower-right-move origin) {origin (lower-right-adjacent origin)}))

(defn diagonally-connected-board [board origin]
  "make connection for jupming diagonally, if connections aren't out of bound, else return same board."
  (if (<= (lower-right-move origin) (max-num (nrows board)))
    (-> board
        (origin-dia-connected-board origin)
        (lower-left-connected-board origin)
        (lower-right-connected-board origin))
    board))

(defn origin-right-connected-board [board origin]
  "Board with origin's right connections made."
  (add-conns board origin {(right-move origin) (right-adj origin)}))

(defn right-connected-board [board origin]
  "Board with the connections of the right move of origin made."
  (add-conns board (right-move origin) {origin (right-adj origin)}))

(defn horizontally-connected-board [board origin]
  "make connection for jumping left to right"
  (let [last-num-in-row (nth triangular-seq (dec (row-num origin)))
        is-last-in-row (= origin last-num-in-row)
        is-second-last-in-row (= origin (dec last-num-in-row))
        horizontal-moves-exist (and (not is-last-in-row) (not is-second-last-in-row))]
    (if horizontal-moves-exist
      (-> board
          (origin-right-connected-board origin)
          (right-connected-board origin))
      board)))

(defn unpegged-board [num-rows]
  {:nrows num-rows
   :holes (loop [i 1 board (sorted-map)]
            (if (> i (max-num num-rows)) board
                (recur
                 (inc i)
                 (assoc
                  board
                  i
                  {:pegged true, :connections {}}))))})

(defn board-nrows [num-rows]
  "Board of num-rows rows"
  (let [board-numbers (range 1 (inc (max-num num-rows)))
        new-board (unpegged-board num-rows)]
    (reduce
     (fn [board num]
       (-> board
           (horizontally-connected-board num)
           (diagonally-connected-board num)))
     new-board
     board-numbers)))


;; ======================================State Transition=======================================

(defn can-jump? [board origin dest]
  (contains? (connections board origin) dest))

(defn valid-move? [board origin dest]
  (every? true?
          [(is-pegged? board origin)
           (can-jump? board origin dest)
           (is-pegged? board (in-between board origin dest))]))

(defn peg-at-loc-moved [board peg-loc val]
  "Set peg-loc's pegged value to val."
  (assoc-in board [:holes peg-loc :pegged] val))

(defn jumped-board [board origin dest]
  "Return board with the jump made if the jump is legal, return the same board otherwise."
  (if (valid-move? board origin dest)
    (-> board
        (peg-at-loc-moved origin false)
        (peg-at-loc-moved (in-between board origin dest) false)
        (peg-at-loc-moved dest true))
    board))

(defn valid-move-exists? [board origin]
  "True if there are legal moves from origin, false otherwise."
  (let [valid-dests (keys (connections board origin))
        valid-move-from-origin? (partial valid-move? board origin)]
    (not-every?
     false?
     (map
      valid-move-from-origin?
      valid-dests))))

(defn is-game-over? [board]
  (let [origins (keys (:holes board))]
    (every? false? (map #(valid-move-exists? board %) origins))))

;; ===============================Ui and User Interactions======================================

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

;; =======================================Visualization=========================================

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
    (let [start (inc (nth triangular-seq (- row-number 2)))
          end (inc (nth triangular-seq (dec row-number)))]
      (range start end))))

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

;; ===================================End of Source============================================
;; (greeting)
;; (def board (atom (board-nrows (get-num-rows))))
;; (def first-removal (convert-to-number (get-first-removal)))
;; (swap! board assoc-in [:holes first-removal :pegged] false)
;; (print-board @board)
;; (while (not (is-game-over? @board))
;;   (do (let [move (get-user-answer "Enter your move")
;;             origin (convert-to-number (str (first move)))
;;             dest (convert-to-number (str (second move)))]
;;         (swap! board jumped-board origin dest))
;;       (print-board @board)))

;; "f d" breaks everything?
;;  aO       
;; bO cO     
;; d@ eO f@    
;; g@ h@ i@ j@  
;; k@ l@ m@ n@ o@
;; 

;; *** How to write this better? I.e. less bugs and more readable ***

;; Bug Logs here:
;; 1. command where there is also only letter => Caused by: java.lang.NullPointerException

;; at clojure.lang.RT.intCast(RT.java:1216)
;; at frank_peg_game.core$convert_to_number.invokeStatic(core.clj:459)
;; at frank_peg_game.core$convert_to_number.invoke(core.clj:458)
;; at frank_peg_game.core$eval358.invokeStatic(core.clj:513)
;; at frank_peg_game.core$eval358.invoke(core.clj:510)
;; at clojure.lang.Compiler.eval(Compiler.java:7176)
;; at clojure.lang.Compiler.load(Compiler.java:7635)
;; ...
;; 2. commands of 3 or more characters like "da'" are accepted
;; 3. when game finishes, no prompt, and it yields NPE sometimes
;;       a-
;;     b- c-
;;    d@ e- f-
;;  g- h- i- j-
;; k@ l@ m- n- o@
;; Enter your move
;; km
;;       a-
;;     b- c-
;;    d@ e- f-
;;  g- h- i- j-
;; k- l- m@ n- o@
;; Exception in thread "main" Syntax error compiling at (/private/var/folders/tk/r0yh5b1d7zlgbfdj4fbddjkm0000gn/T/form-init5261698557887260098.clj:1:125).
;; 	at clojure.lang.Compiler.load(Compiler.java:7647)
;; 	at clojure.lang.Compiler.loadFile(Compiler.java:7573)
;; 	at clojure.main$load_script.invokeStatic(main.clj:452)
;; 	at clojure.main$init_opt.invokeStatic(main.clj:454)
;; 	at clojure.main$init_opt.invoke(main.clj:454)
;; 	at clojure.main$initialize.invokeStatic(main.clj:485)
;; 	at clojure.main$null_opt.invokeStatic(main.clj:519)
;; 	at clojure.main$null_opt.invoke(main.clj:516)
;; 	at clojure.main$main.invokeStatic(main.clj:598)
;; 	at clojure.main$main.doInvoke(main.clj:561)
;; 	at clojure.lang.RestFn.applyTo(RestFn.java:137)
;; 	at clojure.lang.Var.applyTo(Var.java:705)
;; 	at clojure.main.main(main.java:37)
;; Caused by: java.lang.Exception: Cannot find anything to run for: frank-peg-game.core
;; 	at user$eval140.invokeStatic(form-init5261698557887260098.clj:1)
;; 	at user$eval140.invoke(form-init5261698557887260098.clj:1)
;; 	at clojure.lang.Compiler.eval(Compiler.java:7176)
;; 	at clojure.lang.Compiler.eval(Compiler.java:7166)
;; 	at clojure.lang.Compiler.load(Compiler.java:7635)
;; 	... 12 more

;; =====================================TESTSUITE==============================================

(def test-board-3
  {:nrows 3,
   :holes {1 {:pegged true, :connections {}}
           2 {:pegged true, :connections {}}
           3 {:pegged true, :connections {}}
           4 {:pegged true, :connections {}}
           5 {:pegged true, :connections {}}
           6 {:pegged true, :connections {}}}})

(def test-board-3-top-removed
  {:nrows 3,
   :holes
   {1 {:pegged false, :connections {4 2, 6 3}},
    2 {:pegged true, :connections {}},
    3 {:pegged true, :connections {}},
    4 {:pegged true, :connections {1 2, 6 5}},
    5 {:pegged true, :connections {}},
    6 {:pegged true, :connections {1 3, 4 5}}}})

;; ===========================Creating the Board ========================================

(is (= (take 5 triangular-seq) '(1 3 6 10 15)))

(is (= (row-num 2) 2))

(is (= (row-num 5) 3))

(is (= (row-num 9) 4))

(is (= (lower-left-move 1) 4))

(is (= (lower-left-move 5) 12))

(is (= (lower-left-move 3) 8))

(is (= (lower-left-move 6) 13))

(is (= (lower-right-move 1) 6))

(is (= (lower-right-move 5) 14))

(is (= (lower-right-move 3) 10))

(is (= (lower-right-move 6) 15))

(is (= (lower-right-move 4) 13))

(is (= (lower-left-adjacent 1) 2))

(is (= (lower-left-adjacent 5) 8))

(is (= (lower-left-adjacent 3) 5))

(is (= (lower-left-adjacent 6) 9))

(is (= (lower-left-adjacent 4) 7))

(is (= (lower-right-adjacent 1) 3))

(is (= (lower-right-adjacent 5) 9))

(is (= (lower-right-adjacent 3) 6))

(is (= (lower-right-adjacent 6) 10))

(is (= (lower-right-adjacent 4) 8))

(is (= (diagonally-connected-board test-board-3 1)
       {:nrows 3,
        :holes {1 {:pegged true, :connections {4 2, 6 3}}
                2 {:pegged true, :connections {}}
                3 {:pegged true, :connections {}}
                4 {:pegged true, :connections {1 2}}
                5 {:pegged true, :connections {}}
                6 {:pegged true, :connections {1 3}}}}))

(is (= (horizontally-connected-board (diagonally-connected-board test-board-3 1) 4)
       {:nrows 3,
        :holes {1 {:pegged true, :connections {4 2, 6 3}}
                2 {:pegged true, :connections {}}
                3 {:pegged true, :connections {}}
                4 {:pegged true, :connections {1 2, 6 5}}
                5 {:pegged true, :connections {}}
                6 {:pegged true, :connections {1 3, 4 5}}}}))

(is (= (horizontally-connected-board (diagonally-connected-board test-board-3 1) 5)
       {:nrows 3,
        :holes {1 {:pegged true, :connections {4 2, 6 3}}
                2 {:pegged true, :connections {}}
                3 {:pegged true, :connections {}}
                4 {:pegged true, :connections {1 2}}
                5 {:pegged true, :connections {}}
                6 {:pegged true, :connections {1 3}}}}))

(is (= (board-nrows 3)
       {:nrows 3,
        :holes
        {1 {:pegged true, :connections {4 2, 6 3}},
         2 {:pegged true, :connections {}},
         3 {:pegged true, :connections {}},
         4 {:pegged true, :connections {1 2, 6 5}},
         5 {:pegged true, :connections {}},
         6 {:pegged true, :connections {1 3, 4 5}}}}))

(is (= (board-nrows 5)
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

(is (=
     (valid-move?
      test-board-3-top-removed
      1
      4)
     false))

(is (=
     (valid-move?
      test-board-3-top-removed
      1
      6)
     false))

(is (=
     (valid-move?
      test-board-3-top-removed
      1
      3)
     false))

(is (=
     (valid-move?
      test-board-3-top-removed
      4
      1)
     true))

(is (=
     (valid-move?
      test-board-3-top-removed
      6
      1)
     true))

(is (=
     (jumped-board test-board-3-top-removed 4 1)
     {:nrows 3,
      :holes
      {1 {:pegged true, :connections {4 2, 6 3}},
       2 {:pegged false, :connections {}},
       3 {:pegged true, :connections {}},
       4 {:pegged false, :connections {1 2, 6 5}},
       5 {:pegged true, :connections {}},
       6 {:pegged true, :connections {1 3, 4 5}}}}))

(is (=
     (jumped-board test-board-3-top-removed 3 1)
     test-board-3-top-removed))

(is (=
     (is-game-over? {:nrows 3,
                     :holes
                     {1 {:pegged false, :connections {4 2, 6 3}},
                      2 {:pegged false, :connections {}},
                      3 {:pegged false, :connections {}},
                      4 {:pegged true, :connections {1 2, 6 5}},
                      5 {:pegged false, :connections {}},
                      6 {:pegged true, :connections {1 3, 4 5}}}})
     true))

(is (=
     (is-game-over? {:nrows 3,
                     :holes
                     {1 {:pegged false, :connections {4 2, 6 3}},
                      2 {:pegged false, :connections {}},
                      3 {:pegged true, :connections {}},
                      4 {:pegged false, :connections {1 2, 6 5}},
                      5 {:pegged true, :connections {}},
                      6 {:pegged true, :connections {1 3, 4 5}}}})
     false))

(is (= (into [] (row-seq 3)) [4 5 6]))

(is (= (into [] (row-seq 1)) [1]))

(is (= (into [] (row-seq 5)) [11 12 13 14 15]))


;; ======================================Design==================================================
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
   :holes {1 {:pegged true, :connections {}}
           2 {:pegged true, :connections {}}
           3 {:pegged true, :connections {}}
           4 {:pegged true, :connections {}}
           5 {:pegged true, :connections {}}
           6 {:pegged true, :connections {}}}})
(def board0
  {:nrows 3,
   :holes {1 {:pegged true, :connections {4 2, 6 3}}
           2 {:pegged true, :connections {}}
           3 {:pegged true, :connections {}}
           4 {:pegged true, :connections {1 2, 6 5}}
           5 {:pegged true, :connections {}}
           6 {:pegged true, :connections {1 3, 4 5}}}})
;; Say we picked "a" to initialize the game
(def board1
  {:nrows 3,
   :holes {1 {:pegged false, :connections {4 2, 6 3}}
           2 {:pegged true, :connections {}}
           3 {:pegged true, :connections {}}
           4 {:pegged true, :connections {1 2, 6 5}}
           5 {:pegged true, :connections {}}
           6 {:pegged true, :connections {1 3, 4 5}}}})

;; Say we do "da"


(def board2
  {:nrows 3,
   :holes {;; Completion State Check:
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
           6 {:pegged true, :connections {1 3, 4 5}}}})

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
