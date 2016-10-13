(define (problem ark-discourse)

  (:domain ark-discourse-tests)

  ; these objects do nothing, but will receive NoneType error if deleted; solve issue at pddlToGraphs
  (:objects steal - step
            excavate - step
            has-ark - literal
            ark - item
            indy - actor)

  (:init )

  (:goal-action dummy_goal

     ; // these parameters become objects
     :parameters (?excavate - step ?steal - step ?has-ark - literal ?ark - item ?indy - actor)

     ; // preconditions are goals
     :precondition (and (bel-effect ?has-ark ?excavate) (bel-occurs ?steal)
                (bel-occurs ?excavate))

     ; // keep this here for now, should be empty though
     :effect ()

     ; // this forms the initial ingredients for the elements in the plan.
     :decomp (and (name ?excavate excavate)
                  (name ?steal steal)
                  (name ?ark ark)
                  (name ?indy indiana)
                  (name ?has-ark has)
                  (truth ?has-ark True)
                  (nth-lit-arg 0 ?has-ark ?indy)
                  (nth-lit-arg 1 ?has-ark ?ark)
                  (effect ?excavate ?has-ark)
                  (precond ?steal ?has-ark)
                  (linked-by ?excavate ?steal ?has-ark)
                  ))
 )