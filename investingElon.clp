
;;;======================================================
;;; 
;;;   Find the best trades based on Elon Musk's personality
;;;    
;;;
;;;     CLIPS Version 6.4 Example
;;;
;;;     To execute, merely load, reset and run.
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
  (focus QUESTIONS CHOOSE-QUALITIES TRADES PRINT-RESULTS))

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
;;* TRADE QUESTIONS *
;;*******************

(defmodule TRADE-QUESTIONS (import QUESTIONS ?ALL))

(deffacts TRADE-QUESTIONS::question-attributes
  (question (attribute main-component)
            (the-question "Do you prefer to trade in index funds, cryptocurrency, or stocks? ")
            (valid-answers index cryptocurrency stocks unknown))
  (question (attribute has-tech)
            (precursors main-component is stocks)
            (the-question "Would you like the stock to be in technology? ")
            (valid-answers yes no unknown))
  (question (attribute has-dipped)
            (the-question "Has the price gone down recently? ")
            (valid-answers yes no unknown))
  (question (attribute dip)
            (precursors has-dipped is yes)
            (the-question "Has the price gone down greater than 5, 10, 15, or 20%? Answers acceptable: 5,10,15, or 20. Unknown is acceptable. ")
            (valid-answers dip 5 10 15 20 unknown))
  (question (attribute fear)
            (the-question "How well can you control your fear when trading? Bad, average, or well? Unknown is acceptable. ")
            (valid-answers bad average well unknown))
  (question (attribute preferred-risk)
            (the-question "Do you prefer less risky, average risky, or very risky trades? Acceptable answers: Less, Average, Risky, Unknown ")
            (valid-answers less average risky unknown))
  (question (attribute preferred-term)
            (the-question "Do you generally prefer short or long term trades? Acceptable answers: Short, Long, Unknown ")
            (valid-answers short long unknown))
  (question (attribute preferred-type)
            (the-question "Do you generally prefer trendy, established, or unpopular trades? Acceptable answers: Trendy, Established, Unpopular, Unknown ")
            (valid-answers trendy established unpopular unknown))) 
 
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
;;* CHOOSE TRADE QUALITIES RULES *
;;*******************************

(defmodule CHOOSE-QUALITIES (import RULES ?ALL)
                            (import QUESTIONS ?ALL)
                            (import MAIN ?ALL))

(defrule CHOOSE-QUALITIES::startit => (focus RULES))

(deffacts elon-trade-rules

  ; Elon's for picking the best risk

  (rule (if has-dipped is yes and 
            dip is 20)
        (then best-risk is risky))

  (rule (if fear is bad)
        (then best-risk is less))

  (rule (if fear is average)
        (then best-risk is less with certainty 85 and
              best-risk is average with certainty 70 and
              best-risk is risky with certainty 35))

  (rule (if fear is well)
        (then best-risk is average with certainty 85 and
              best-risk is risky with certainty 65))

  (rule (if has-dipped is yes and
            dip is 15)
        (then best-risk is average with certainty 85 and
              best-risk is very with certainty 65))

  (rule (if preferred-risk is risky)
        (then best-risk is risky with certainty 70))

  (rule (if preferred-risk is average)
        (then best-risk is average with certainty 85))

  (rule (if preferred-risk is less) 
        (then best-risk is less with certainty 75))

  (rule (if preferred-risk is less and
            best-risk is risky)
        (then best-risk is average))

  (rule (if preferred-risk is risky and
            best-risk is less)
        (then best-risk is average))

  (rule (if preferred-risk is unknown) 
        (then best-risk is less with certainty 65 and
              best-risk is average with certainty 65 and
              best-risk is risky with certainty 45))

  ; Rules for picking the best term

  (rule (if main-component is index)
        (then best-term is long with certainty 90
        and best-industry is market with certainty 90))
    
      (rule (if main-component is unknown)
        (then best-term is long with certainty 90
        and best-industry is stocks with certainty 90 and
        best-industry is cryptocurrency with certainty 80))

  (rule (if main-component is stocks and
            has-dipped is no)
        (then best-term is long with certainty 75 and
              best-term is short with certainty 40))

  (rule (if main-component is stocks and
            has-dipped is yes)
        (then best-term is long with certainty 95 and
              best-term is short with certainty 35))

  (rule (if main-component is cryptocurrency)
        (then best-term is long with certainty 65 and
            best-industry is cryptocurrency with certainty 70))

  (rule (if main-component is-not cryptocurrency and
            has-dipped is yes and
            dip is 20)
        (then best-term is long))

  (rule (if has-dipped is yes and
            dip is 15)
        (then best-term is long with certainty 75))
                   
  (rule (if preferred-term is short)
        (then best-term is short with certainty 80))

  (rule (if preferred-term is long)
        (then best-term is long with certainty 80))

  (rule (if preferred-term is unknown)
        (then best-term is short with certainty 40 and
              best-term is long with certainty 85))
  
  ; Rules for picking the best type of trade

  (rule (if has-dipped is yes and dip is 15)
        (then best-type is unpopular with certainty 45 and
              best-type is established with certainty 90))

  (rule (if preferred-type is trendy)
        (then best-type is trendy with certainty 55))

  (rule (if preferred-type is established)
        (then best-type is established with certainty 90))

  (rule (if preferred-type is unpopular)
        (then best-type is unpopular with certainty 20))

  (rule (if best-type is unpopular and
            preferred-type is trendy)
        (then best-type is established))

  (rule (if best-type is trendy and
            preferred-type is unpopular) 
        (then best-type is established))

  (rule (if preferred-type is unknown)
        (then best-type is trendy with certainty 55 and
              best-type is established with certainty 75 and
              best-type is unpopular with certainty 45))

      
      
      
      ; Best stock trade by industry

  (rule (if has-tech is yes)
        (then best-industry is tech with certainty 85 and
              best-industry is food with certainty 30 and
              best-industry is entertainment with certainty 30))

      (rule (if has-tech is no)
        (then best-industry is tech with certainty 40 and
              best-industry is food with certainty 30 and
              best-industry is entertainment with certainty 20))

)



;;************************
;;* TRADE SELECTION RULES *
;;************************

(defmodule TRADES (import MAIN ?ALL))

(deffacts any-attributes
  (attribute (name best-term) (value any))
  (attribute (name best-risk) (value any))
  (attribute (name best-type) (value any))
  (attribute (name best-industry) (value any)))

(deftemplate TRADES::trade
  (slot name (default ?NONE))
  (multislot term (default any))
  (multislot risk (default any))
  (multislot type (default any))
  (multislot industry (default any)))

(deffacts TRADES::the-trade-list 
  (trade (name Dogecoin) (term long) (risk average) (type established) (industry cryptocurrency))
  (trade (name CocaCola) (term long) (risk less) (type established) (industry food))
  (trade (name McDonalds) (term long) (risk less) (type established) (industry food))
  (trade (name Tesla) (term long) (risk less) (type established) (industry tech))
  (trade (name SpaceX) (term long) (risk less) (type established) (industry tech))
  (trade (name FegToken) (term short) (risk average) (type unpopular) (industry cryptocurrency))
  (trade (name ShibaInu) (term short) (risk risky) (type unpopular) (industry cryptocurrency))
  (trade (name Apple) (term long) (risk risky) (type established) (industry tech))
  (trade (name Bitcoin) (term long)(risk average) (type established) (industry cryptocurrency))
  (trade (name Gamestop) (term short) (risk risky) (type trendy) (industry entertainment))
  (trade (name SnP500) (term long) (risk less) (type established) (industry market)) 
  (trade (name Google) (term long) (risk less) (type established) (industry tech))
  (trade (name AMC) (term long) (risk risky) (type trendy) (industry entertainment))
  (trade (name Amazon) (term long) (risk less) (type established) (industry tech)))
  
(defrule TRADES::generate-trades
  (trade (name ?name)
        (term $? ?c $?)
        (risk $? ?b $?)
        (type $? ?s $?)
        (industry $? ?q $?))
  (attribute (name best-term) (value ?c) (certainty ?certainty-1))
  (attribute (name best-risk) (value ?b) (certainty ?certainty-2))
  (attribute (name best-type) (value ?s) (certainty ?certainty-3))
  (attribute (name best-industry) (value ?q) (certainty ?certainty-4))
  =>
  (assert (attribute (name trade) (value ?name)
                     (certainty (min ?certainty-1 ?certainty-2 ?certainty-3 ?certainty-4)))))

;;*****************************
;;* PRINT SELECTED TRADE RULES *
;;*****************************

(defmodule PRINT-RESULTS (import MAIN ?ALL))

(defrule PRINT-RESULTS::header ""
   (declare (salience 10))
   =>
   (println)
   (println "        SELECTED TRADES" crlf)
   (println " TRADE                  Elon's Certainty")
   (println " ----------------------------------------------------------------")
   (assert (phase print-trades)))

(defrule PRINT-RESULTS::print-trade ""
  ?rem <- (attribute (name trade) (value ?name) (certainty ?per))		  
  (not (attribute (name trade) (certainty ?per1&:(> ?per1 ?per))))
  =>
  (retract ?rem)
  (format t " %-24s %2d%%%n" ?name ?per))

(defrule PRINT-RESULTS::end-spaces ""
   (not (attribute (name trade)))
   =>
   (println))


