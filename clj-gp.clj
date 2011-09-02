
; Linear genetic programming system in clojure.
;
; © jcadwal@gmail.com
; Released under GPLv3

; Works cited:
; [1] Brameier, Markus. "On Linear Genetic Programming". 2004. 
; [2] Koza, John. Genetic Programming. 1992.
  

(ns main
  (:import (java.lang Math)
	   (javax.imageio ImageIO)
	   (java.awt.image BufferedImage)
	   (java.util.concurrent Executors))
  (:use [clojure.contrib.str-utils :only (re-split)])
  (:use	[clojure.contrib.duck-streams :only (read-lines)]))

			
(set! *warn-on-reflection* true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;(helpers)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn get-effs [prog]
  "Returns the effective instructions of a register 
   machine program [1]"
  (let [updt (fn [[curr effs :as state] idx]               
               (let [[op a b c]     (prog idx)
                     [op* a* b* c*] (if (> idx 0)
                                      (prog (dec idx))
                                      nil)					    
                     brnch?         (= :gte op*)
                     one?           (or (= :sin op)
                                      (= :cos op))] 
                 (if (and (contains? curr a)
                       (not= :gte op))
                   (vector
                     (if one?
                       (-> curr (disj a)(conj b))
                       (-> curr (disj a)(conj b)(conj c)))
                     (if brnch?
                       (conj effs idx (dec idx))
                       (conj effs idx)))
                   state)))
        finl (reduce updt
               (vector #{0} [])
               (reverse
                 (range
                   (count prog))))]
    finl))

;;Following functions for converting
;;a program to dot-language representation
(defn- get-edges [p]
  (let [edges (vector (first p)
                (map #(if (vector? %)
                        (first %) 
                        %) 
                  (rest p)))]
    (if (some vector? p)
      (cons edges
        (mapcat get-edges (filter vector? (rest p))))
      (vector edges))))


(defn- get-nodes [edg]
  (let [updt (fn [nodes [head child]]
               (apply conj nodes
                 head
                 child))]
    (reduce updt #{} edg)))


(defn to-dot [prog]
  "Returns dot-language representation of a program"
  (let [edges (get-edges (to-nested prog))
        nodes (get-nodes edges)]
    (with-out-str
      (println "digraph G{")
      (doseq [[head child] edges]	
        (println (format "%s -> {%s}"
                   (head :id)
                   (with-out-str
                     (doseq [ch (map #(if (map? %) (% :id) %) child)]
                       (print ch " "))))))
      (doseq [n nodes]
        (println (format "%s [label=\"%s\"]" (n :id) (n :label))))
      (println "}"))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;comp-mdl
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;
;;;;;;;;;;;linear
;;;;;;;;;;;;;;;;;


(defn linear []
  "Returns a collection of functions for generating, running,
   and mutating a register machine program"
  (let [intp  (fn [{:keys [regs flag] :as env} [op a b c]]                
                (case op
                  :add (assoc-in env [:regs a] (+ (regs b)(regs c)))
                  :sub (assoc-in env [:regs a] (- (regs b)(regs c)))		      
                  :mul (assoc-in env [:regs a] (mod
                                                 (* (regs b)(regs c))
                                                 100000))
                  :div (assoc-in env [:regs a] (if (or (> (regs c) 0.00001)
                                                     (< (regs c) -0.00001))
                                                 (/ (regs b)(regs c))
                                                 (regs a)))
                  :sin (assoc-in env [:regs a]
                         (java.lang.Math/sin (regs b)))
                  :cos (assoc-in env [:regs a]
                         (java.lang.Math/cos (regs b)))		      
                  :gte (if (>= (regs a)(regs b))
                         (assoc env :flag true)
                         env)))
        
        ops [:add :sub :gte :sin :mul :div :cos]]
  
    {:ops ops

     :gen (fn [params]
            (let [size  (+ (rand-int (params :max))
                          (params :min))
                  nargs (params :nargs)]
              (vec (for [_ (range size)] 
                     (vector (rand-nth ops)
                       (rand-int nargs)
                       (rand-int nargs)
                       (rand-int nargs))))))    
     

     :run (fn [prog regs]
            (let [updt (fn [env ins]
                         (if (env :flag)
                           (assoc env :flag false)
                           (intp env ins)))
                  finl (reduce updt
                         {:regs regs :flag false}
                         prog)]              
              (finl :regs)))

     :vary (fn [prog params #^java.util.Random r]
             (let [siz   (count prog)
                   nargs (params :nargs)]
               (case (rand-nth [:shk :grw :mut])
                 :shk (if (> siz 1)
                        (let [effs (second (get-effs prog))
                              idx  (if (empty? effs)
                                     (.nextInt r siz)
                                     (effs (.nextInt r (count effs))))]                          
                          (vec
                            (concat (subvec prog 0 idx)
                              (subvec prog (inc idx) siz))))
                        prog)
		     
                 :grw (let [idx (.nextInt r siz)
                            
                            arg (if (> siz 3)
                                  (let [e (vec (first (get-effs (vec (drop (dec idx) prog)))))]
                                    (nth e (.nextInt r (count e))))
                                  (.nextInt r nargs))                            

                            ins (vector (nth ops (.nextInt r (count ops)))
                                  arg
                                  (.nextInt r nargs)
                                  (.nextInt r nargs))]
				    
                        (vec
                          (concat (subvec prog 0 idx)
                            [ins]
                            (subvec prog idx siz))))
                 
                 :mut (let [idx (.nextInt r siz) 
                            arg (inc (.nextInt r 3))
                            nrg (rand-nth
                                  (vec
                                    (first (get-effs (vec (drop idx prog))))))
                            mut (assoc-in prog [idx arg] nrg)]
                        mut))))

     :show (fn [prog]
             (doseq [i prog]
               (print i " ")))}))
   

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;lrn-algs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;
;;;;;single-based
;;;;;;;;;;;;;;;;;
(comment
(defn random [cmp prbm evals]
  "Implements random-search learning algorithm"
  (let [gen  (cmp :gen)
        run  (cmp :run)
        show (cmp :show)
        valu (prbm :valu)
        btr? (prbm :btr?)
        prof (prbm :prof)]
    (loop [best (gen 20 5)
           bfit (valu best run)
           cntr 0]
      (if (> cntr evals)
        (do (prof best run show bfit) bfit)
        (let [new (gen 20 5)
              fit (valu new run)]
          (if (btr? fit bfit)
            (recur  new
              fit
              (inc cntr))
            (recur  best
              bfit
              (inc cntr))))))))
);comment
									
;;;;;;;;;;;;;;;;;
;;;;;populn-based
;;;;;;;;;;;;;;;;;

(defn ptourn [cmp prbm params]
  "Implements tournament-based evolution
  on parallel processors"
  (let [gen  (cmp :gen)
        run  (cmp :run)
        show (cmp :show)
        vary (cmp :vary)
        valu (prbm :valu)
        btr? (prbm :btr?)
        prof (prbm :prof)
        psiz (params :psiz)
        grup (params :grup)

        popn (vec 
               (pmap (fn [_]
                       (let [ind (RegMach/gen (params :min)
                                   (params :max)
                                   (params :nargs)
                                   (MersenneTwisterFast.))
                             fit (valu ind run)]
                         (atom (vector ind fit))))
                 (range psiz)))

        nthr (.. Runtime getRuntime availableProcessors)

        pool (Executors/newFixedThreadPool nthr)

        tsks (map (fn [th]
                    (let [r (MersenneTwisterFast.)]
                      (fn []
                        (dotimes [i (/ (- (params :evals) psiz) nthr)]
                          (let [tourn (sort
                                        #(btr? (@(popn %1) 1)
                                               (@(popn %2) 1))
                                        (repeatedly grup #(.nextInt r psiz)))
                                winnr (@(popn (first tourn)) 0)
                                loser (popn (last tourn))
                                newbi (let [newb (RegMach/vary winnr (params :nargs) r)
                                            fit (valu newb run)]
                                        (vector newb fit))]

                            (reset! loser newbi))))))		    
               (range nthr))	

        finl (do
               (println "before invoke")
               (time
                 (doseq [futr (.invokeAll pool tsks)]
                   (.get futr))
                 )
               (println "after invoke")
               (.shutdown pool)
               (sort #(btr? (%1 1) (%2 1)) (map deref popn)))

        best (first finl)]

    (do      
      (prof (best 0) show (best 1))
      (best 1))))



(defn tourn [cmp prbm params]
  "Serial tournament evolution"
  (let [gen  (cmp :gen)
        run  (cmp :run)
        show (cmp :show)
        vary (cmp :vary)
        valu (prbm :valu)
        btr? (prbm :btr?)
        prof (prbm :prof)
        psiz (params :psiz)
        grup (params :grup)

        popn (vec
               (pmap 
                 (fn [_]
                   (let [ind (gen params)
                         fit (valu ind run)]
                     (vector ind fit))) 
                 (range psiz)))
	
        updt (fn [popn curr]
               (let [tourn (sort
                             #(btr? (get-in popn [%1 1])                                
                                (get-in popn [%2 1]))
                             (repeatedly grup #(rand-int psiz)))
                     winnr (get-in popn [(first tourn) 0])
                     loser (last tourn)
                     newbi (let [new (vary winnr params)
                                 fit (valu new run)]
                             (vector new fit))]
                 (assoc popn loser newbi)))

        finl (sort #(btr? (%1 1) (%2 1))
               (time (reduce updt popn (range psiz (params :evals)))))
        
        best (first finl)]

    (do
      ;(prof (best 0) run show (best 1))
      (best 1))))
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;problems
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn two-spl []
  "Returns a collection of functions for evaluating the 
   performance of a problem on the classic machine learning
   two-spiral problem [2]."
  (let [data (into []
               (for [line (if (= "Windows 7" (System/getProperty "os.name"))
                            (read-lines "c:\\My Dropbox\\code\\datasets\\spiral.csv")
                            (read-lines "/home/john/Dropbox/code/datasets/spiral.csv"))]                 
                 (vec
                   (map #(Float/parseFloat %)
                     (re-split #"," line)))))]

    {:valu (fn [prog run]			
             (reduce (fn [sum [a b ans]]
                       (let [result (if (> 0.0
                                          (aget (RegMach/run prog
                                                  (float-array
                                                    [a b 1.0 1.0 1.0 1.0 1.0]))
                                            0))
				      
                                      1.0
                                      -1.0)]
                         (if (= ans result) (inc sum) sum)))
               0
               data))
     
     :btr? (fn [v1 v2] (if (> v1 v2) true false))

     :prof (fn [prog show val]
             (let [str (with-out-str			 
                         (println "\nConfirm: "
                           (reduce (fn [sum [a b ans]]
                                     (let [result (if (> 0.0
                                                        (aget (RegMach/run
                                                                prog
                                                                (float-array
                                                                  [a b 1.0 1.0 1.0 1.0 1.0]))
                                                          0))
							   
                                                    1.0
                                                    -1.0)
                                           sum    (if (= ans result)(inc sum) sum)]
                                       (do
                                         ;(println a b ans result sum)
                                         sum)))
                             0
                             data))
                         (println "Value: " val)
					
                         (show prog))]
               (spit "2spl.log" str :append true))
             prog)}))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;benching
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;The following functions bench the given learning algorithms

(defn pbench [{:keys [lrn-alg 
                      cmp-mdl
                      problem 
                      params  
                      times]}]
  (pmap (fn [_] (lrn-alg cmp-mdl problem params)) (range times)))


(defn bench [{:keys [lrn-alg 
                     cmp-mdl
                     problem
                     params
                     times]}]
  (doall
    (for [i (range times)]
      (do (println "\nTrial " i)
        (lrn-alg cmp-mdl problem params)))))
			
(defn bench-all [runs]
  (println "\n/====BEGIN====\\")  
  (doseq [run runs]    
    (println (run :report))
    (spit "2spl.log" (run :report) :append true)
    (println "\nResult: " (sort > (bench run))))
  (println "\n\\=====END=====/\n\n"))
		
(defn runs []
  (let [times 15
        evals 200000
        prblm (two-spl)	]
    (for [psiz [10 100 1000 10000 100000]
          gsiz [2 3 5 10 50 100 1000]
          :when (< gsiz psiz)]
      {:lrn-alg ptourn
       :cmp-mdl (linear)
       :problem prblm
       :params  {:max        20       ;starting max size
                 :min        5        ;starting min size
                 :nargs      7        ;number of regs, incl inputs
                 :ops        []
                 :evals      evals    ;total number of evals

                 ;population-based specfic
                 :psiz       psiz
                 :grup       gsiz
                 :publish    4000}
	
       :times   times                  ;number times to benchmark
       :report  (format "\n\nptourn/linear/two-spl/%d/%d/%d/%d" times evals psiz gsiz)})))


(bench-all (runs))



     
  
  
