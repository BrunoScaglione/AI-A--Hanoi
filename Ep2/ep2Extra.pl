frontier([0]).
node_ref(node_num, state, cost, previous_action).
father(child_node_num, father_node_num).
min_cost(inf).
best_node(0).
num_nodes(0).
h(0).
action_list([]).

all_moves([
    move(a,b),
    move(a,c),
    move(b,a),
    move(b,c),
    move(c,a),
    move(c,b),
    move(a,table),
    move(b,table),
    move(c,table)
]).

is_list_empty([]).

stack_ruined(0).

ordered_goals(orderedgoals).
stack_mask(stackmask).

:- dynamic(on/2).
:- dynamic(node_ref/4).
:- dynamic(father/2).
:- dynamic(frontier/1).
:- dynamic(min_cost/1).
:- dynamic(best_node/1).
:- dynamic(num_nodes/1).
:- dynamic(h/1).
:- dynamic(counter/1).
:- dynamic(action_list/1).
:- dynamic(right_goal_seq/1).
:- dynamic(ordered_goals/1).
:- dynamic(stack_mask/1).


free(table).
free(B) :- 
    not(on(_,B)).

on(_,_) :- false.

return_plan(EXPLORED_NODES, COST, ACTION_LIST) :- 
    ordered_goals(GOALS),
    node_ref(GOAL_NODE, GOALS, COST, _),
    num_nodes(EXPLORED_NODES),
    actions(GOAL_NODE),
    action_list(ACTION_LIST).

create_father(NODE) :-
    num_nodes(NUM_NODES),
    assertz(father(NODE, NUM_NODES)).

update_frontier(NODE) :-
    num_nodes(NUM_NODES),
    frontier(FRONTIER_NODES),
    delete(FRONTIER_NODES, NODE, AUX),
    append(AUX, [NUM_NODES], NEW_FRONTIER),
    retractall(frontier(_)),
    assertz(frontier(NEW_FRONTIER)).

update_counter(NUM_NODES) :-
    % Atualiza o predicado num_nodes
    retractall(num_nodes(_)),
    AUX is NUM_NODES+1,
    assertz(num_nodes(AUX)).

move_preconditions(X,Y):-
    % preconditions
    (X \== table),
    X \== Y,
    free(X),
    free(Y),
    on(X,Z),
    Z \== Y.

record_state(NEXT_STATE3) :-
    on(a,X),
    append([], [on(a,X)], NEXT_STATE),
    on(b,Y),
    append(NEXT_STATE, [on(b,Y)], NEXT_STATE2),
    on(c,Z),
    append(NEXT_STATE2, [on(c,Z)], NEXT_STATE3).

move_effects(X,Y) :-
    % remove effects
    retractall(on(X,_)),
    % add effects
    assertz(on(X,Y)).

move(X,Y):-
    num_nodes(NUM_NODES),
    best_node(NODE),
    node_ref(NODE, STATE, FATHER_COST, _),
    assert_state(STATE),
    (
        move_preconditions(X,Y) ->
            (
                N1 is NUM_NODES+1, F1 is FATHER_COST+1,
                move_effects(X,Y),
                record_state(NEXT_STATE),
                retract_state(NEXT_STATE),
                assertz(node_ref(N1, NEXT_STATE, F1, [X,Y])),
                update_counter(NUM_NODES),
                create_father(NODE),
                update_frontier(NODE)
            );
            (
                true
            )
    ).

assert_state([]).
assert_state(STATE) :-
    [H|T] = STATE,
    assertz(H),
    assert_state(T).

retract_state([]).
retract_state(STATE) :-
    [H|T] = STATE,
    retractall(H),
    retract_state(T).

list_of_clauses2clauses([]).
list_of_clauses2clauses(LISTOFCLAUSES) :-
    [H|T] = LISTOFCLAUSES,
    H,
    list_of_clauses2clauses(T).

reached_goals(GOALS) :-
    best_node(NODE),
    node_ref(NODE, STATE, _, _),    
    assert_state(STATE),
    (
        list_of_clauses2clauses(GOALS) ->
            (
                retract_state(STATE),
                true
            );
            (
                retract_state(STATE),
                false
            )
    ).

create_children :-
    best_node(NODE),
    node_ref(NODE, _, _, FATHER_ACTION)
    [X, Y] = FATHER_ACTION,
    allmoves(ALL_MOVES)
    delete(ALL_MOVES, move(Y,X), TODO_MOVES),
    list_of_clauses2clauses(TODO_MOVES).


% stack is a sequece of predicates corresponding to stacked blocks
% stackmask is a list of booleans. Each boolean correspponds to a goal predicate: 
% if it is 1, the predicate is part of a stack of blocks, else it is not
% obs: dont need to rest stack_ruined to 0 at end of stack because there will 
% never be two stack with 3 block configuration
heuristic(_,[], []) :-
    retractall(h(_)),
    assertz(h(0)),
    retractall(stack_ruined(_)),
    assertz(stack_ruined(0)).
heuristic(NODE_STATE,GOALS, STACK_MASK) :-
    assert_state(NODE_STATE),
    [HEAD|TAIL] = GOALS,
    [HEADMASK|TAILMASK] = STACK_MASK,
    (
        (HEAD, HEADMASK == 0) -> 
            (true);
            (
                (HEAD, HEADMASK == 1, stack_ruined(0)) -> 
                    (
                        true
                    );
                    (   
                        (
                            (not(HEAD), stack_ruined(0)) -> 
                                (
                                    retractall(stack_ruined(_)),
                                    assertz(stack_ruined(1))
                                );(true) 
                        ),
                        h(H),
                        AUX is H+1,
                        retractall(h(_)),
                        assertz(h(AUX))
                    )
            )
    ),
    heuristic(NODE_STATE,TAIL,TAILMASK).

evaluate_nodes([], _, _).
evaluate_nodes(FRONTIER,GOALS,STACK_MASK) :-
    [NODE|OTHER_NODES] = FRONTIER,
    node_ref(NODE,NODE_STATE,COST_TO_NODE,_),
    heuristic(NODE_STATE,GOALS,STACK_MASK),
    h(H),
    % retractall(h(_)), # eh melhor fazer isso dentro de heuristic
    COST is COST_TO_NODE + H,
    min_cost(MIN_COST),
    (
    	COST < MIN_COST -> (   
                           	retractall(min_cost(_)),
                            assertz(min_cost(COST)),
                           	retractall(best_node(_)),
                            assertz(best_node(NODE))
                           );true
    ),
    evaluate_nodes(OTHER_NODES, GOALS, STACK_MASK).

search :-
    frontier(FRONTIER),
    retractall(min_cost(_)),
    assertz(min_cost(inf)),
    retractall(best_node(_)),
    ordered_goals(GOALS),
    stack_mask(STACK_MASK),
    evaluate_nodes(FRONTIER,GOALS,STACK_MASK),
    (   
    	(reached_goals(GOALS)) ->
    		true;
    		(  
                create_children,
                search(GOALS)
            )
    ).

actions(0).
actions(FINAL_NODE) :-
    node_ref(FINAL_NODE, _, _, ACTION),
    action_list(AUX),
    append([ACTION], AUX, ACTION_LIST),
    retractall(action_list(_)),
    assertz(action_list(ACTION_LIST)),
    father(FATHER, FINAL_NODE),
    actions(FATHER).

order_2_goals(on(X,Y), on(W,Z), ORDERED_2_GOALS, SAMESTACK) :-
    (
        (W \== Y, Z \== X) -> 
            (
                0 == SAMESTACK,
                % not on the same stack
                [on(X,Y), on(W,Z)] == ORDERED_2_GOALS
            ); 
            (   
                1 == SAMESTACK,
                % need to order, on the same stack
                (
                    (W == Y) ->
                    (
                        [on(X,Y), on(W,Z)] == ORDERED_2_GOALS
                    );
                    (
                        [on(X,Y), on(W,Z)] == ORDERED_2_GOALS
                    )
                )
            )
    ).

order_goals(GOALS) :-
    % goals are ordered if they correspond to goals in the same stack
    % the order is from the predictes that go from bottom to the top of th stack
    % example: ordergoals([on(a,b), on(c,a), on(b,table)], ORDERED_GOALS) has 
    % ORDERED_GOALS being [on(b,table), on(a,b), on(c,a)]
    [GOAL0|T] = GOALS,
    (   % if T is empty list []
        (is_list_empty(T)) -> 
            (
                retractall(ordered_goals(_)),
                assertz(ordered_goals(GOALS)),
                retractall(stack_mask(_)),
                assertz(stack_mask([0]))
            );
            (   % if T has one goal
                ([GOAL1|TT] = T, is_list_empty(TT)) -> 
                    (
                        order_2_goals(GOAL0,GOAL1,ORDERED_GOALS,SAMESTACK0)
                        (
                            SAMESTACK0 == 0 -> 
                            (
                                retractall(stack_mask(_)),
                                assertz(stack_mask([0, 0]))
                            );
                            (
                                retractall(stack_mask(_)),
                                assertz(stack_mask([1, 1]))
                            )
                        )
                    );
                    (   % else T has to have 2 goals
                        order_2_goals(GOAL0,GOAL1,ORDERED_2_GOALS1, SAMESTACK1),
                        [G1, G2] = ORDERED_2_GOALS1,
                        (
                            (SAMESTACK1 == 0) -> 
                                (
                                    [GOAL1, GOAL2] = T,
                                    order_2_goals(GOAL0,GOAL2,ORDERED_2_GOALS2, SAMESTACK2),
                                    [G3, G4] = ORDERED_2_GOALS2,
                                    order_2_goals(GOAL1,GOAL2,ORDERED_2_GOALS3, SAMESTACK3),
                                    [G5, G6] = ORDERED_2_GOALS3,
                                    (
                                        (SAMESTACK3 == 0) -> 
                                        (
                                            retractall(ordered_goals(_)),
                                            assertz(ordered_goals([G3, G4, G5])),
                                            retractall(ordered_goals(_)),
                                            assertz(ordered_goals([G3, G4, G5])),
                                            (
                                                (SAMESTACK2 == 0) -> 
                                                    (
                                                        retractall(stack_mask(_)),
                                                        assertz(stack_mask([0, 0, 0]))
                                                    );
                                                    (
                                                        retractall(stack_mask(_)),
                                                        assertz(stack_mask([1, 1, 0]))
                                                    )
                                            )
                                        );
                                        (
                                            (SAMESTACK2 == 0) -> 
                                                (
                                                    retractall(ordered_goals(_)),
                                                    assertz(ordered_goals([G5, G6, G3])),
                                                    retractall(stack_mask(_)),
                                                    assertz(stack_mask([1, 1, 0]))
                                                );(true)
                                        )
                                    )
                                );
                                (
                                    [GOAL1, GOAL2] = T,
                                    order_2_goals(GOAL1,GOAL2,ORDERED_2_GOALS4, SAMESTACK4),
                                    [G7, G8] = ORDERED_2_GOALS4,
                                    (
                                        (SAMESTACK3 == 0) -> 
                                            (
                                                retractall(ordered_goals(_)),
                                                assertz(ordered_goals([G1, G2, G8])),
                                                retractall(stack_mask(_)),
                                                assertz(stack_mask([1, 1, 0]))
                                            );
                                            (
                                                retractall(stack_mask(_)),
                                                assertz(stack_mask([1, 1, 1])),
                                                (G7 == G1) -> 
                                                    (
                                                        order_2_goals(GOAL0,GOAL2,ORDERED_2_GOALS5, SAMESTACK5),
                                                        [G9, G10] = ORDERED_2_GOALS5,
                                                        retractall(ordered_goals(_)),
                                                        assertz(ordered_goals([G7, G9, G10]))
                                                    );
                                                    (
                                                        (G8 == G2) -> 
                                                            (
                                                                order_2_goals(GOAL0,GOAL2,ORDERED_2_GOALS6, SAMESTACK6),
                                                                [G11, G12] = ORDERED_2_GOALS6,
                                                                retractall(ordered_goals(_)),
                                                                assertz(ordered_goals([G11, G12, G8]))
                                                            );
                                                            (
                                                                (G7 == G2) -> 
                                                                    (
                                                                        retractall(ordered_goals(_)),
                                                                        assertz(ordered_goals([G1, G2, G8]))
                                                                    );
                                                                    (   % G8 == G1
                                                                        retractall(ordered_goals(_)),
                                                                        assertz(ordered_goals([G7, G8, G2]))
                                                                    )
                                                            )
                                                    )
                                            )
                                    )
                                )
                        )

                    )           
            )
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

modify_initial_state(INITIAL_STATE) :-
    retractall(node_ref(0,_,0,_)),
    assertz(node_ref(0, INITIAL_STATE, 0, 'INIT')).

main(INITIAL_STATE, GOALS, EXPLORED_NODES, COST, ACTION_LIST) :-
    modify_initial_state(INITIAL_STATE),
    % need goals ordered from base to top to do the heuristic correctly
    ordered_goals(GOALS),
    search,
    return_plan(EXPLORED_NODES, COST, ACTION_LIST).