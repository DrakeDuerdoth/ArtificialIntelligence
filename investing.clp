
;;;======================================================
;;;   Fear of Investing Program
;;;
;;;     This program will help you decide if your 
;;;     trade is a good one based on the certainty of 
;;;     Warren Buffet. 
;;;
;;;     To execute, (load "Investing.clp"), (reset), then (run)
;;;======================================================

(defmodule MAIN (export ?ALL))

;;****************
;;* DEFFUNCTIONS *
;;****************

(deffunction MAIN::ask-question (?question ?allowed-values)
   (print ?question)
   (bind ?answer (read))
   (if (lexemep ?answer) then (bind ?answer (lowcase ?answer)))
   (while (not (member$ ?answer ?allowed-values)) do
      (print ?question)
      (bind ?answer (read))
      (if (lexemep ?answer) then (bind ?answer (lowcase ?answer))))
   ?answer)

;;*****************
;;* INITIAL STATE *
;;*****************

(deftemplate MAIN::attribute
   (slot name)
   (slot value)
   (slot certainty (default 100.0)))

(defrule MAIN::start
  (declare (salience 10000))
  =>
  (set-fact-duplication TRUE)
  (focus QUESTIONS CHOOSE-QUALITIES STOCKS PRINT-RESULTS))

(defrule MAIN::combine-certainties ""
  (declare (salience 100)
           (auto-focus TRUE))
  ?rem1 <- (attribute (name ?rel) (value ?val) (certainty ?per1))
  ?rem2 <- (attribute (name ?rel) (value ?val) (certainty ?per2))
  (test (neq ?rem1 ?rem2))
  =>
  (retract ?rem1)
  (modify ?rem2 (certainty (/ (- (* 100 (+ ?per1 ?per2)) (* ?per1 ?per2)) 100))))
  
;;******************
;;* QUESTION RULES *
;;******************

(defmodule QUESTIONS (import MAIN ?ALL) (export ?ALL))

(deftemplate QUESTIONS::question
   (slot attribute (default ?NONE))
   (slot the-question (default ?NONE))
   (multislot valid-answers (default ?NONE))
   (slot already-asked (default FALSE))
   (multislot precursors (default ?DERIVE)))
   
(defrule QUESTIONS::ask-a-question
   ?f <- (question (already-asked FALSE)
                   (precursors)
                   (the-question ?the-question)
                   (attribute ?the-attribute)
                   (valid-answers $?valid-answers))
   =>
   (modify ?f (already-asked TRUE))
   (assert (attribute (name ?the-attribute)
                      (value (ask-question ?the-question ?valid-answers)))))

(defrule QUESTIONS::precursor-is-satisfied
   ?f <- (question (already-asked FALSE)
                   (precursors ?name is ?value $?rest))
         (attribute (name ?name) (value ?value))
   =>
   (if (eq (nth$ 1 ?rest) and) 
    then (modify ?f (precursors (rest$ ?rest)))
    else (modify ?f (precursors ?rest))))

(defrule QUESTIONS::precursor-is-not-satisfied
   ?f <- (question (already-asked FALSE)
                   (precursors ?name is-not ?value $?rest))
         (attribute (name ?name) (value ~?value))
   =>
   (if (eq (nth$ 1 ?rest) and) 
    then (modify ?f (precursors (rest$ ?rest)))
    else (modify ?f (precursors ?rest))))

;;*******************
;;* Stocks QUESTIONS *
;;*******************

(defmodule Stock-QUESTIONS (import QUESTIONS ?ALL))

(deffacts STOCK-QUESTIONS::question-attributes
  (question (attribute main-trade)
            (the-question "Would you prefer a trade in stocks, index funds, cryptocurrency, or unknown? ")
            (valid-answers stocks index cryptocurrency foreign unknown))
  (question (attribute potential-pattern)
            (precursors main-trade is cryptocurrency)
            (the-question "Are you seeing any potential pattern in the price? Unknown is also an acceptable answer. ")
            (valid-answers yes no unknown))
  (question (attribute has-dipped)
            (the-question "Has the market gone down more than 30% in the last 3 months? Unknown is also an acceptable answer. ")
            (valid-answers yes no unknown))
  (question (attribute low-high)
            (precursors has-dipped is yes)
            (the-question "Is the price unusually low? ")
            (valid-answers low high))
  (question (attribute familiar)
            (the-question "Are you somewhat familar, unfamiliar, familiar, or very familiar with the stock/cryptocurrency? ")
            (valid-answers familiar unfamiliar somewhat very))
  (question (attribute hodl)
            (the-question "Do you prefer long term or short term trades? Unknown is also an acceptable answer. ")
            (valid-answers long short unknown))
  (question (attribute on-tech)
            (the-question "Do you prefer trading something based on technology or food? Unknown is also an acceptable answer. ")
            (valid-answers technology food unknown))
  (question (attribute stock-or-crypto)
            (the-question "Do you prefer to trade with stocks, cryptocurrency, or index funds? Unknown is also an acceptable answer. ")
            (valid-answers stock cryptocurrency index unknown))) 
 
;;******************
;; The RULES module
;;******************

(defmodule RULES (import MAIN ?ALL) (export ?ALL))

(deftemplate RULES::rule
  (slot certainty (default 100.0))
  (multislot if)
  (multislot then))

(defrule RULES::throw-away-ands-in-antecedent
  ?f <- (rule (if and $?rest))
  =>
  (modify ?f (if ?rest)))

(defrule RULES::throw-away-ands-in-consequent
  ?f <- (rule (then and $?rest))
  =>
  (modify ?f (then ?rest)))

(defrule RULES::remove-is-condition-when-satisfied
  ?f <- (rule (certainty ?c1) 
              (if ?attribute is ?value $?rest))
  (attribute (name ?attribute) 
             (value ?value) 
             (certainty ?c2))
  =>
  (modify ?f (certainty (min ?c1 ?c2)) (if ?rest)))

(defrule RULES::remove-is-not-condition-when-satisfied
  ?f <- (rule (certainty ?c1) 
              (if ?attribute is-not ?value $?rest))
  (attribute (name ?attribute) (value ~?value) (certainty ?c2))
  =>
  (modify ?f (certainty (min ?c1 ?c2)) (if ?rest)))

(defrule RULES::perform-rule-consequent-with-certainty
  ?f <- (rule (certainty ?c1) 
              (if) 
              (then ?attribute is ?value with certainty ?c2 $?rest))
  =>
  (modify ?f (then ?rest))
  (assert (attribute (name ?attribute) 
                     (value ?value)
                     (certainty (/ (* ?c1 ?c2) 100)))))

(defrule RULES::perform-rule-consequent-without-certainty
  ?f <- (rule (certainty ?c1)
              (if)
              (then ?attribute is ?value $?rest))
  (test (or (eq (length$ ?rest) 0)
            (neq (nth$ 1 ?rest) with)))
  =>
  (modify ?f (then ?rest))
  (assert (attribute (name ?attribute) (value ?value) (certainty ?c1))))

;;*******************************
;;* CHOOSE TRADE QUALITY RULES *
;;*******************************

(defmodule CHOOSE-QUALITIES (import RULES ?ALL)
                            (import QUESTIONS ?ALL)
                            (import MAIN ?ALL))

(defrule CHOOSE-QUALITIES::startit => (focus RULES))

(deffacts the-stock-rules

  ; Rules for picking the best body

  (rule (if has-dipped is yes and 
            has-dipped is yes)
        (then best-trade is long))

  (rule (if familar is unfamiliar)
        (then best-trade is short))

  (rule (if familar is somewhat)
        (then best-trade is long with certainty 30 and
              best-trade is short with certainty 60))

  (rule (if familar is very)
        (then best-trade is short with certainty 40 and
              best-trade is long with certainty 80))

  (rule (if has-dipped is yes and
            low-high is long)
        (then best-trade is short with certainty 40 and
              best-trade is long with certainty 60))

  (rule (if hodl is long)
        (then best-trade is long with certainty 40))

  (rule (if hodl is unknown)
        (then best-trade is short with certainty 20))

  (rule (if hodl is short) 
        (then best-trade is short with certainty 40))

  (rule (if hodl is short and
            best-trade is long)
        (then best-trade is unknown))

  (rule (if hodl is long and
            best-trade is short)
        (then best-trade is unknown))

  (rule (if hodl is unknown) 
        (then best-trade is short with certainty 20 and
              best-trade is unknown with certainty 20 and
              best-trade is long with certainty 20))

  ; Rules for picking the best stock

  (rule (if main-trade is stocks)
        (then on-tech is technology with certainty 90))

  (rule (if main-trade is cryptocurrency and
            has-dipped is no)
        (then best-on-tech is technology with certainty 90 and
              best-on-tech is food with certainty 30))

  (rule (if main-trade is cryptocurrency and
            has-dipped is yes)
        (then best-on-tech is technology with certainty 80 and
              best-on-tech is food with certainty 50))

  (rule (if main-trade is index)
        (then best-on-tech is technology))

  (rule (if main-trade is-not index and
            has-dipped is yes and
            low-high is low)
        (then best-on-tech is technology))

  (rule (if has-dipped is yes and
            low-high is high)
        (then best-on-tech is food with certainty 40))
                   
  (rule (if on-tech is technology)
        (then best-on-tech is technology with certainty 40))

  (rule (if on-tech is food)
        (then best-on-tech is food with certainty 40))

  (rule (if on-tech is unknown)
        (then best-on-tech is technology with certainty 20 and
              best-on-tech is food with certainty 20))
  
  ; Rules for picking the best sweetness

  (rule (if has-dipped is yes and
            low-high is high)
        (then best-stock-or-crypto is index with certainty 90 and
              best-stock-or-crypto is cryptocurrency with certainty 40))

  (rule (if is-crypto is no)
        (then best-stock-or-crypto is stock with certainty 40))

  (rule (if is-crypto is yes)
        (then best-stock-or-crypto is index with certainty 50))

  (rule (if is-crypto is yes)
        (then best-stock-or-crypto is index with certainty 40))

  (rule (if best-stock-or-crypto is index and
            stock-or-crypto is stocks)
        (then best-stock-or-crypto is cryptocurrency))


  (rule (if stock-or-crypto is unknown)
        (then best-stock-or-crypto is stocks with certainty 20 and
              best-stock-or-crypto is index with certainty 20 and
              best-stock-or-crypto is cryptocurrency with certainty 20))

)

;;************************
;;* STOCK SELECTION RULES *
;;************************

(defmodule stocks (import MAIN ?ALL))

(deffacts any-attributes
  (attribute (name best-trade) (value any))
  (attribute (name best-on-tech) (value any))
  (attribute (name best-stock-or-crypto) (value any)))

(deftemplate stocks::stock
  (slot name (default ?NONE))
  (multislot trade (default any))
  (multislot on-tech (default any))
  (multislot stock-or-crypto (default any)))

(deffacts stocks::the-stock-list 
  (stocks (name Dogecoin) (on-tech yes) (body medium) (sweetness medium sweet))
  (stocks (name Coca-Cola) (on-tech no) (body light) (sweetness dry))
  (stocks (name McDonalds) (on-tech no) (body medium) (sweetness dry))
  (stocks (name Tesla) (on-tech yes) (body medium full) (sweetness medium dry))
  (stocks (name SpaceX) (on-tech yes) (body light) (sweetness medium dry))
  (stocks (name Amazon) (on-tech yes) (body light medium) (sweetness medium sweet))
  (stocks (name Microsoft) (on-tech yes) (body full))
  (stocks (name Apple) (on-tech yes) (body light) (sweetness medium sweet))
  (stocks (name Bitcoin) (on-tech yes) (body light))
  (stocks (name Ethereum) (on-tech yes) (sweetness dry medium))
  (stocks (name SnP500) (on-tech no) (sweetness dry medium))
  (stocks (name Google) (on-tech yes) (body medium) (sweetness medium))
  (stocks (name Sony) (on-tech yes) (body full))
  (stocks (name GM) (on-tech yes) (sweetness dry medium)))
  
(defrule stocks::generate-stocks
  (stock (name ?name)
        (trade $? ?c $?)
        (on-tech $? ?b $?)
        (stock-or-crypto $? ?s $?))
  (attribute (name best-trade) (value ?c) (certainty ?certainty-1))
  (attribute (name best-on-tech) (value ?b) (certainty ?certainty-2))
  (attribute (name best-stock-or-crypto) (value ?s) (certainty ?certainty-3))
  =>
  (assert (attribute (name stock) (value ?name)
                     (certainty (min ?certainty-1 ?certainty-2 ?certainty-3)))))

;;*****************************
;;* PRINT SELECTED STOCK RULES *
;;*****************************

(defmodule PRINT-RESULTS (import MAIN ?ALL))

(defrule PRINT-RESULTS::header ""
   (declare (salience 10))
   =>
   (println)
   (println "        SELECTED STOCKS" crlf)
   (println " Stock                  CERTAINTY")
   (println " -------------------------------")
   (assert (phase print-stocks)))

(defrule PRINT-RESULTS::print-stock ""
  ?rem <- (attribute (name stock) (value ?name) (certainty ?per))		  
  (not (attribute (name stock) (certainty ?per1&:(> ?per1 ?per))))
  =>
  (retract ?rem)
  (format t " %-24s %2d%%%n" ?name ?per))

(defrule PRINT-RESULTS::remove-poor-stock-choices ""
  ?rem <- (attribute (name stock) (certainty ?per&:(< ?per 20)))
  =>
  (retract ?rem))

(defrule PRINT-RESULTS::end-spaces ""
   (not (attribute (name stock)))
   =>
   (println))
