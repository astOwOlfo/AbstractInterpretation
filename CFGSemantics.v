From AbstractInterpretation Require Import CFG Expression ExpressionSemantics Environment.

From Coq Require Import Structures.OrderedType ZArith.

Section CFGSemantics.

Context {node_id_set : nat -> Prop}.

Definition node_id : Set :=
  { id : nat | node_id_set id }.

Variable (initial_node : node_id).

Definition state : Type := node_id * environment.

Definition initial_state : state :=
  (initial_node, initial_environment).

Variant instruction_small_step : instruction -> environment -> environment -> Prop :=
  
  | SSkip   (env :             environment) :
      instruction_small_step Skip env env

  | SAssign (env :             environment)
            (var_id :          var_id)
            (expr :            int_expression)
            (result :          Z)
            (Hexpr_result :    int_expression_evaluates env expr result) :
      instruction_small_step (Assign var_id expr) env (assign var_id result env)

  | SGuard  (env :             environment)
            (condition :       bool_expression)
            (Hcondition_true : bool_expression_evaluates env condition true) :
      instruction_small_step (Guard condition) env env
      
  | SAssert (env :             environment)
            (condition :       bool_expression)
            (Hcondition_true : bool_expression_evaluates env condition true) :
      instruction_small_step (Assert condition) env env.


Variant instruction_fails_assertion : instruction -> environment -> Prop :=
  | FailsAssertion (env :              environment)
                   (condition :        bool_expression)
                   (Hcondition_false : bool_expression_evaluates env condition false) :
      instruction_fails_assertion (Assert condition) env.


Variant small_step (cfg : cfg) : state -> state -> Prop :=
  | SmallStep (env env' :     environment)
              (arc :          arc)
              (Harc :         In arc cfg.(carcs))
              (Hinstruction : instruction_small_step arc.(ainstruction) env env') :
      small_step cfg (arc.(asource), env) (arc.(adestination), env').

End CFGSemantics.