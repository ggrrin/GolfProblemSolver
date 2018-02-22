% social Golfer Problem, ktery je ve slidech prikladem vhodneho tematu? 
% 
% Pokud jsem tedy spravne nasel jeho definici -> http://mathworld.wolfram.com/SocialGolferProblem.html
% 
% Pokud to dobre chapu solver by mel vzit 3 parametry n, k, d takove, ze:
% n .... pocet hracu golfu
% k .... velikost skupiny, ktera hraje spolu v jeden den
% d .... pocet dnu turnaje
% pricemz mus platit k*d=n
% 
% a hledame takove rozhozeni hracu do skupin, ze plat:
% kazdy hrac hraje prave jednou kazdy den
% kazdy hrac je ve skupine s jinym hracem nejvyse jednou 
%
% - kazdy den hraji vsichni hraci
% - skupin je n choose k
% 
% - v kazdem dni 
% (A) priradim kazdemu hraci skupinu
% vs
% (B) priradim kazdemu mistu ve skupine hrace
% vs
% (C) generovat rovnou inteligentne
% 
% (A)
% 5^20 k
% (1) podminka: kazda skupina ma prave 4 hrace
% 
% (B)
% 20^20
% (1a) podminka: hraci se ve skupine neopakuji
% (1b) podminka: kazdy hrac je pouze v jedne skupine 
% 
% 
% -pro vsechny skupiny mezi dny 
% (2) podminka: kazdy hrac hralje s kazdym nejvyse 1
% 

:- use_module(library(clpfd)).
:- use_module(library(assoc)).

% n = 4
% k = 2
% g = 2
% d = 3 

golf(DaysAttendance, N, K, G, D) :- 
	build_model(N, D, DaysAttendance, Variables),
	domain(Variables, 1, G),
	%group_size_satisfy(DaysAttendance, G, K),
	testx(DaysAttendance),
	labeling([],Variables).

build_model(N, D, DaysAttendance, Variables) :- build_model_ac(N, D, 0, DaysAttendance, Variables, []).
build_model_ac(_, D, D, [], V, V).
build_model_ac(N, D, DAcumulator, [X|DaysAttendance],  Variables, VariablesAcumulator) :- DAcumulator < D,
	build_day(N, X, 0), append(VariablesAcumulator, X, Vars), Dc is DAcumulator + 1, 
	build_model_ac(N, D, Dc, DaysAttendance, Variables, Vars).

build_day(N, [], N).
build_day(N, [_|Players], Nc) :- Nc < N,
	Ncc is Nc + 1, 
	build_day(N, Players, Ncc).

group_size_satisfy([], _, _).
group_size_satisfy([D|PlayerGroupAssignments], G, N) :- 
	group_size_satisfy_day(1, D, G, N),
	group_size_satisfy(PlayerGroupAssignments, G, N). 

group_size_satisfy_day(G, D, G, N) :- exactly(G, D, N).
group_size_satisfy_day(Gc, D, G, N) :- Gc < G,
	exactly(Gc, D, N), Gcc is Gc + 1,
	group_size_satisfy_day(Gcc, D, G, N).

exactly(_, [], 0).
exactly(X, [Y|L], N) :-
        X #= Y #<=> B,
        N #= M+B,
        exactly(X, L, M).

:- use_module(library(clpfd)).

testx(P) :-
	suspensions(P, Suspensions),
	fd_global(testx(P), empty, Suspensions).
	
				     
suspensions([], []).
suspensions([D|DaysAttendance], Suspensions) :-
	suspensions_day(D, Suspensions, SLast),
	suspensions(DaysAttendance, SLast).

suspensions_day([], SLast, SLast).
suspensions_day([P|Attendance], [val(P)|Suspensions], SLast) :-
	suspensions_day(Attendance, Suspensions, SLast).

:- use_module(library(avl)).

:- multifile clpfd:dispatch_global/4.
clpfd:dispatch_global(testx(P), Sin, Sout, Actions) :-
	%Actions = [],
	%Sin = Sout,
	%moc(P).

	get_grounded_vars(P, Sin, Sout, GroundRec),
	(ground(GroundRec) -> 
	P = [D|_],
	init_DpDiffSets(D, DpDiffSets),
	get_actions(P, 1, GroundRec, DpDiffSets, Actions)
	;
	Actions = []).

moc(P) :- true.

init_DpDiffSets([], []).
init_DpDiffSets([_|D], [X|Xs]) :-
	empty_fdset(X),
	init_DpDiffSets(D, Xs).

%day(Day,pl(DayIndex, PlayerIndex, PlayerGround)) :-
%GroundRec storing played Day variable, index and
% player variable and index

% get_actions(+AttendanceDays, +DayIndex, +GroundRec, +DpDiffSets, -Actions ) :-
% iterates over days which are processed in pairs for actions
% with currently played day, which is naturally skipped
get_actions([], _, day(Dp, _), DpDiffSets, Actions) :- create_DpActions(Dp, DpDiffSets, Actions).
get_actions([_|AttendanceDays], DayIndex, GroundRec, DpDiffSets, Actions) :- % skip played day
	day(_, pl(DayIndex, _, _)) = GroundRec,
	NDayIndex is 1 + DayIndex,
	get_actions(AttendanceDays, NDayIndex, GroundRec, DpDiffSets, Actions).
get_actions([D|AttendanceDays], DayIndex, GroundRec, DpDiffSets, Actions) :- % process actions in not played days
	day(_, pl(DayIndex, _, _)) \= GroundRec,
	process_actions(D, GroundRec, DpDiffSets, DpDiffSetsOut, Actions, LastAction),	
	NDayIndex is 1 + DayIndex,
	get_actions(AttendanceDays, NDayIndex, GroundRec, DpDiffSetsOut, LastAction). 


% process_actions(+D, +GroundRec, +DpDiffSets, -DpDiffSetsOut, +Actions, -LastAction) :-
process_actions(D, day(Dp,pl(_,PlayerIndex, DpN)), DpDiffSets, DpDiffSetsOut, Actions, LastAction) :-
	find_dN_var(D, 1, PlayerIndex, Dn),
	(fd_var(Dn) -> process_unboundN_actions(Dp, D, Dn, DpN, Actions, LastAction),
	DpDiffSets = DpDiffSetsOut
	;
	process_boundN_actions(Dp, D, Dn, DpN, Actions, LastAction),
	process_DpDiffSets(D, Dp, DpN, Dn,  DpDiffSets, DpDiffSetsOut)
	).
	%TODO fail actions

% create_DpActions(+Dp, +DpDiffSets, +Actions) :-
% create actions subtracting all invalid fdsets values from Dp
create_DpActions([], [], []).
create_DpActions([D|Dp], [_|DpDiffSets], Actions) :-
	ground(D),
	create_DpActions(Dp, DpDiffSets, Actions).
create_DpActions([D|Dp], [Diff|DpDiffSets], [D in_set ReducedSet|Actions]) :-
	fd_var(D),
	fd_set(D, Set), 
	fdset_subtract(Set, Diff, ReducedSet),
	create_DpActions(Dp, DpDiffSets, Actions).


%find_dN_var(+Day, +CIndex, +PlayerIndex, -Dn) :-
% returns variable at PlayerIndex in Res
find_dN_var([P|_], PlayerIndex, PlayerIndex, P).
find_dN_var([_|D], CIndex, PlayerIndex, Res) :- 
	CIndex =\= PlayerIndex,
	NCIndex is 1 + CIndex,
	find_dN_var(D, NCIndex, PlayerIndex, Res). 


% process_boundN_actions(+Dp, +D, +Dn, +DpN, +Actions, -ActionLast) :-
% create actions to remove incompatible values from Domains of D
% Dp played day assignments ; D other day assignments
% DpN player assignment in played day player
% Dn player assgnment in other day player
process_boundN_actions([], [], _, _, ActionLast, ActionLast).
process_boundN_actions([DpI|Dp], [Di|D], Dn, DpN, Actions, ActionLast) :- %skip
	(fd_var(DpI); DpI =\= DpN; ground(Di)), 
	process_boundN_actions(Dp, D, Dn, DpN, Actions, ActionLast).
process_boundN_actions([DpI|Dp], [Di|D], Dn, DpN, [Di in_set ReducedSet|Actions], ActionLast) :-
	ground(DpI), DpI =:= DpN, fd_var(Di), %played index is not var thus gonna fail 
	fd_set(Di, Set), 
	fdset_del_element(Set, Dn, ReducedSet),
	process_boundN_actions(Dp, D, Dn, DpN, Actions, ActionLast).
	
% process_DpDiffSets(+D, +Dp, +DpN, +Dn,  +DpDiffSets, -DpDiffSetsOut) :-
% adds to DpDiffSets incompatible values
process_DpDiffSets([], [], _, _, [], []).
process_DpDiffSets([DpI|Dp], [Di|D], Dn, DpN, [X|DpDiffSets], [X|DpDiffSetsOut]) :- %skip
	(fd_var(Di); Di =\= Dn; ground(DpI)), 
	process_DpDiffSets(Dp, D, Dn, DpN, DpDiffSets, DpDiffSetsOut).
process_DpDiffSets([DpI|Dp], [Di|D], Dn, DpN, [DpIDS|DpDiffSets], [DpIDSOut|DpDiffSetsOut]) :-
	ground(Di), Di =:= Dn, fd_var(DpI), 
	fdset_add_element(DpIDS, DpN, DpIDSOut),
	process_DpDiffSets(Dp, D, Dn, DpN, DpDiffSets, DpDiffSetsOut).

%GColumnIndex-GColumnLower-GColumnUpper

% process_unboundN_actions(Dp, D, Dn, DpN, [A|Actions], Actions) :-
% add action removing all incompatible values of Dn
process_unboundN_actions(Dp, D, Dn, DpN, [Dn in_set ReducedSet|Actions], Actions) :-
	fd_set(Dn, DnSet),
	empty_fdset(X),
	get_Dn_invalid_values(Dp, D, DpN, X, DnDiffSet),
	fdset_subtract(DnSet, DnDiffSet, ReducedSet).


% get_Dn_invalid_values(+Dp, +D, +DpN, -DiffSet) :-
% get DiffSet - list of all invalid values in Dn 
get_Dn_invalid_values([], [], _, S, S).
% jump over played column and columns with at least one not grounded cell
get_Dn_invalid_values([DpI|Dp], [Di|D], DpN, DiffSetIn, DiffSetOut) :-
	(fd_var(DpI); fd_var(Di)),
	get_Dn_invalid_values(Dp, D,  DpN, DiffSetIn, DiffSetOut). 
get_Dn_invalid_values([DpI|Dp], [Di|D], DpN, DiffSetIn, DiffSetOut) :-
	ground(DpI), ground(Di), DpN =:= DpI,
	fdset_add_element(DiffSetIn, Di, DiffSetOutEn),
	process_unboundN_actions(Dp, D,  DpN, DiffSetOutEn, DiffSetOut). 


	
% FOLLOWS FINDING OF READY GROUNDED 
	
get_grounded_vars(Attendance, PrevState, NextState, GroundRec) :- %DayIndex, PlayerIndex, PlayerGroup) :-
	iterate_days(Attendance, PrevState, empty, NextState, 1, GroundRec). %pl(DayIndex, PlayerIndex, PlayerGroup).	

iterate_days([], _, S, S, _, _).
iterate_days([D|AttendanceDays], PrevState, NextStateIn, NextStateOut, DayIndex, GroundedRec) :-
	iterate_day(D, PrevState, NextStateIn, NNextStateOut, DayIndex, 1, NGroundRec),
	(ground(NGroundRec), pl(GRDay, _, _) = NGroundRec, GRDay =:= DayIndex ->
	GroundedRec = day(D, NGroundRec) 
	; GroundedRec = NGroundRec
	),
	NDayIndex is 1 + DayIndex,
	iterate_days(AttendanceDays, PrevState, NNextStateOut, NextStateOut, NDayIndex, GroundedRec).
	
iterate_day([], _, S, S, _, _, _).
iterate_day([P|Players], PrevState, NextStateIn, NextStateOut, CDayIndex, CPlayerIndex, GroundedRec) :-
	log_state(P, p(CDayIndex,CPlayerIndex), NextStateIn, NNextStateOut, IsGrounded),
	try_set_grounded(P, p(CDayIndex,CPlayerIndex), IsGrounded, PrevState, GroundedRec, CDayIndex, CPlayerIndex),
	NCPlayerIndex is 1 + CPlayerIndex,
	iterate_day(Players, PrevState, NNextStateOut, NextStateOut, CDayIndex, NCPlayerIndex, GroundedRec). 

log_state(P, Coor, StateIn, StateOut, IsGrounded) :-
	(fd_var(P) -> IsGrounded = 0 ; IsGrounded = 1),
	avl_incr(Coor, StateIn, IsGrounded, StateOut).

try_set_grounded(_, _, 0, _, _, _, _).
try_set_grounded(_, _, 1, _, GR, _, _) :- ground(GR).
try_set_grounded(P, Coor, 1, PrevState, GroundedRec, CDayIndex, CPlayerIndex) :- var(GroundedRec),
	avl_fetch(Coor, PrevState, PrevVal), (PrevVal =:= 0 ->
	GroundedRec = pl(CDayIndex, CPlayerIndex, P);true).
	
			
% the entrypoint
% exactly(I, Xs, N) :-
% 	dom_suspensions(Xs, Susp),
% 	fd_global(exactly(I,Xs,N), state(Xs,N), Susp).
% 
% 
% :- multifile clpfd:dispatch_global/4.
% clpfd:dispatch_global(exactly(I,_,_), state(Xs0,N0), state(Xs,N), Actions) :-
% 	exactly_solver(I, Xs0, Xs, N0, N, Actions).
% 
% exactly_solver(I, Xs0, Xs, N0, N, Actions) :-
% 	ex_filter(Xs0, Xs, N0, N, I),
% 	length(Xs, M),
% 	(   N=:=0 -> Actions = [exit|Ps], ex_neq(Xs, I, Ps)
% 	;   N=:=M -> Actions = [exit|Ps], ex_eq(Xs, I, Ps)
% 	;   N>0, N<M -> Actions = []
% 	;   Actions = [fail]
% 	).
% 
% % exactly.pl
% % rules [1,2]: filter the X's, decrementing N
% ex_filter([], [], N, N, _).  % ex_filter([X|Xs], Ys, L, N, I) :- X==I, !, % 	M is L-1,
% 	ex_filter(Xs, Ys, M, N, I).
% 
% ex_filter([X|Xs], Ys0, L, N, I) :-
% 	fd_set(X, Set),
% 	fdset_member(I, Set), !,
% 	Ys0 = [X|Ys],
% 	ex_filter(Xs, Ys, L, N, I).
% 
% ex_filter([_|Xs], Ys, L, N, I) :-
% 	ex_filter(Xs, Ys, L, N, I).
% 
% % rule [3]: all must be neq I
% ex_neq(Xs, I, Ps) :-
% 	fdset_singleton(Set0, I),
% 	fdset_complement(Set0, Set),
% 	eq_all(Xs, Set, Ps).
% 
% % rule [4]: all must be eq I
% ex_eq(Xs, I, Ps) :-
% 	fdset_singleton(Set, I),
% 	eq_all(Xs, Set, Ps).
% 
% eq_all([], _, []).
% eq_all([X|Xs], Set, [X in_set Set|Ps]) :-
% 	eq_all(Xs, Set, Ps).
% 
