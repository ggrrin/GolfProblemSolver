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
% (1) podminka: kazda skupina ma prave k hrace
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

% n = 4
% k = 2
% g = 2
% d = 3 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Helper testing predicates 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test(DaysAttendance) :-
	golf(DaysAttendance, 4, 2, 2, 2).

test1(S,Ac) :-
	domain([A,B,C], 1, 2),
	pair_constrain_body([[1,1,2,2],[1,A,B,C]], [[ground,ground,ground,ground],[var, var, var, var]], S, Ac).

test2(Z) :-
	domain([A,B,C], 1, 2),
	process_boundN_actions([1,1,2,2], [1,A,B,C], 1, 1, [[],[],[],[]], Z).

test3(Z) :-
	domain([A,B,C], 1, 2),
	process_boundN_actions([1,A,B,C], [1,1,2,2], 1, 1, [[],[],[],[]], Z).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Social Golf problem CSP model 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

golf(DaysAttendance, N, K, G, D) :- 
	build_model(N, D, DaysAttendance, Variables),
	domain(Variables, 1, G),
	group_size_satisfy(DaysAttendance, G, K),
	pair_constrain(DaysAttendance),
	lex_chain(DaysAttendance),
	labeling([],Variables).

golf_t(T, DaysAttendance, N, K, G, D) :- 
	statistics(runtime,[Start|_]),
	golf(DaysAttendance, N, K, G, D),
	statistics(runtime,[Stop|_]),
	T is Stop - Start.

golf_all(DaysAttendance, N, K, G, D) :- 
	build_model(N, D, DaysAttendance, Variables),
	domain(Variables, 1, G),
	group_size_satisfy(DaysAttendance, G, K),
	pair_constrain(DaysAttendance),
	labeling([],Variables).


golf_all_t(T, DaysAttendance, N, K, G, D) :- 
	statistics(runtime,[Start|_]),
	golf_all(DaysAttendance, N, K, G, D),
	statistics(runtime,[Stop|_]),
	T is Stop - Start.

build_model(N, D, DaysAttendance, Variables) :- build_model_ac(N, D, 0, DaysAttendance, Variables, []).
build_model_ac(_, D, D, [], V, V).
build_model_ac(N, D, DAcumulator, [X|DaysAttendance],  Variables, VariablesAcumulator) :- DAcumulator < D,
	build_day(N, X, 0), append(VariablesAcumulator, X, Vars), Dc is DAcumulator + 1, 
	build_model_ac(N, D, Dc, DaysAttendance, Variables, Vars).

build_day(N, [], N).
build_day(N, [_|Players], Nc) :- Nc < N,
	Ncc is Nc + 1, 
	build_day(N, Players, Ncc).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Equal sized groups constrain implementation 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Global pairs constrain implementation 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pair_constrain(P) :-
	suspensions(P, Suspensions),
	next_grounded_state(P, [], Sout, _),
	fd_global(pair_constrain(P), Sout, Suspensions).
	
				     
suspensions([], []).
suspensions([D|DaysAttendance], Suspensions) :-
	suspensions_day(D, Suspensions, SLast),
	suspensions(DaysAttendance, SLast).

suspensions_day([], SLast, SLast).
suspensions_day([P|Attendance], [val(P)|Suspensions], SLast) :-
	suspensions_day(Attendance, Suspensions, SLast).


:- multifile clpfd:dispatch_global/4.
clpfd:dispatch_global(pair_constrain(P), Sin, Sout, Actions) :-
	pair_constrain_body(P, Sin, Sout, Actions).

pair_constrain_body(P, Sin, Sout, Actions) :-
	next_grounded_state(P, Sin, Sout, PlayedRecord),
	invalidateDomains(P, PlayedRecord, InvalidValues),
	gather_actions(P, InvalidValues, Actions).


% gather_actions(+Attandance, +InvalidValues, -Actions) :-
gather_actions([], [], []).
gather_actions([D|Attandance], [DInvalids|InvalidValues], Actions) :-
	gather_day_actions(D, DInvalids, Actions, LastAction),
	gather_actions(Attandance, InvalidValues, LastAction).


% gather_day_actions(D, DInvalids, Actions, LastAction) :-
gather_day_actions([], [], Actions, Actions).
gather_day_actions([P|D], [InvalidSet|DInvalids], Actions, LastAction) :-
	(empty_fdset(InvalidSet) -> 
	ActionsRest = Actions
	;
	fd_set(P, X),
	fdset_subtract(X, InvalidSet, ReducedSet) ,
	[P in_set ReducedSet|ActionsRest] = Actions
	),
	gather_day_actions(D, DInvalids, ActionsRest, LastAction).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Iteration over all grounded vars and executing their invalidation 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% invalidateDomains(+AttendanceDays, +PlayedRecord, -InvalidValues) :-
invalidateDomains(AttendanceDays, PlayedRecord, InvalidValues) :-
	init_DaysDiffSets(AttendanceDays, InvalidValuesIn),
	invalidateDomainsLoop(AttendanceDays, E-E, PlayedRecord, Q-Q, InvalidValuesIn, InvalidValues).

% init_DaysDiffSets([D|AttandanceDays], [X|Xs]) :-
% for each domain variable initialize fdset for invalid values
init_DaysDiffSets([], []).
init_DaysDiffSets([D|AttandanceDays], [X|Xs]) :-
	init_DpDiffSets(D, X),
	init_DaysDiffSets(AttandanceDays, Xs).

init_DpDiffSets([], []).
init_DpDiffSets([_|D], [X|Xs]) :-
	empty_fdset(X),
	init_DpDiffSets(D, Xs).


% invalidateDomainsLoop(+AttendanceDays, [diff]PairDays, +PlayedRecord, [diff]PairsInvalidsBegin, +PairsInvalidEnd, -InvalidValues) :-
% loop over AttandanceDays and update DayPairsInvalidValues if day was played
invalidateDomainsLoop([], _, [], Begin, [], X) :- diff_to_list(Begin, X).
invalidateDomainsLoop([D|AttendanceDays], PairDays, [none|PlayedRecord], PairsInvalidsBegin, [DpInvalids|PairsInvalidEnd], InvalidValues) :-
	% skip not played days
	diff_insert(PairDays, D, PairDaysOut), 
	diff_insert(PairsInvalidsBegin, DpInvalids, K),
	invalidateDomainsLoop(AttendanceDays, PairDaysOut, PlayedRecord, K, PairsInvalidEnd, InvalidValues).
invalidateDomainsLoop([Dp|AttendanceDays], PairDays, [DpRecord|PlayedRecord], PairsInvalidsBegin, [DpInvalids|PairsInvalidEnd], InvalidValues) :-
	DpRecord \= none,
	diff_cp_catL(PairDays, AttendanceDays, A),
	invalidatePairs(A, Dp, DpRecord, PairsInvalidsBegin, DpInvalids, PairsInvalidEnd, PairsInvalidsBeginOut, DpInvalidsOut, PairsInvalidEndOut),
	diff_insert(PairDays, Dp, B),
	diff_insert(PairsInvalidsBeginOut, DpInvalidsOut, C), % [PairsInvalidsBeginOut|DpInvalidsOut]
	invalidateDomainsLoop(AttendanceDays, B, PlayedRecord, C, PairsInvalidEndOut, InvalidValues).

% invalidatePairs(+PairDays, +Dp, +DpRecord, +[diff]PairsInvalidsBegin, +DpInvalids, +PairsInvalidEnd, -[diff]PairsInvalidsBeginOut, -DpInvalidsOut, -PairsInvalidEndOut) :-
% for all pairs p-Dp where p is from PairDays invalidate appropriate subtract fdsets
invalidatePairs([], _, _, _, I, _, Q-Q, I, []).
invalidatePairs([D|PairDays], Dp, DpRecord, [DInvalids|PairsInvalidsBegin]-E, DpInvalids, PairsInvalidEnd, [DInvalidsOut|PairsInvalidsBeginOut]-Q, DpInvalidsOut, PairsInvalidEndOut) :-
	% D days before Dp
	\+ unify_with_occurs_check([DInvalids|PairsInvalidsBegin], E),
	updateDayPairsInvalidValues(D, Dp, F-F, C-C, DpRecord, [DInvalids|DpInvalids], [DInvalidsOut|DpInvalidsOutX]),
	invalidatePairs(PairDays, Dp, DpRecord, PairsInvalidsBegin-E, DpInvalidsOutX, PairsInvalidEnd, PairsInvalidsBeginOut-Q, DpInvalidsOut, PairsInvalidEndOut).
invalidatePairs([D|PairDays], Dp, DpRecord, E-E1, DpInvalids, [DInvalids|PairsInvalidEnd], Q-Q, DpInvalidsOut, [DInvalidsOut|PairsInvalidEndOut]) :-
	% D days after Dp
	unify_with_occurs_check(E,E1),
	updateDayPairsInvalidValues(D, Dp, F-F, C-C, DpRecord, [DInvalids|DpInvalids], [DInvalidsOut|DpInvalidsOutX]),
	invalidatePairs(PairDays, Dp, DpRecord, E-E1, DpInvalidsOutX, PairsInvalidEnd, _, DpInvalidsOut, PairsInvalidEndOut).
	

% updateDayPairsInvalidValues(+D, +Dp, +[diff]DAc, +[diff]DpAc, +DpRecord, +InvalidValuesIn, +InvalidValues) :- 
% for each player selected in DpRecord invalid values computation is done
% D other day to process
% Dp played day to process
% DAc processed players acumulator
% DpAc processed played players acumulator
% DpRecord bit map determinig if player was played (none vs ground)
% InvalidsValuesIn = [DInvalids|DpInvalids] so far gathered invalids for D resp. Dp days
% InvalidsValuesOut = [DInvalidsOut|DpInvalidsOut] updated invalids for D resp. Dp days
updateDayPairsInvalidValues([], [], _, _, [], X, X).
updateDayPairsInvalidValues([Di|D], [DpI|Dp], DAc, DpAc, [none|DpRecord], InvalidValuesIn, InvalidValues) :- 
	%skip not played players
	diff_insert(DAc, Di, DAcOut), %[DAc|Di]
	diff_insert(DpAc, DpI, DpAcOut), %[DpAc|DpI]
	updateDayPairsInvalidValues(D, Dp, DAcOut, DpAcOut, DpRecord, InvalidValuesIn, InvalidValues).
updateDayPairsInvalidValues([Dn|D],  [DpN|Dp], DAc, DpAc, [ground|DpRecord], [DInvalids|DpInvalids], InvalidValues) :- 
	diff_cp_catL(DAc, [Dn|D], DDay), % DDay = [DAc|[Dn|D]],
	diff_cp_catL(DpAc,[DpN|Dp], DpDay), % DpDay = [DpAc|[DpN|Dp]],
	(fd_var(Dn) ->  process_unboundN_actions(DpDay, DDay, DAc, DpN, DInvalids, DInvalidsOut), % C.
	DpInvalidsOut = DpInvalids
	;
	process_boundN_actions(DpDay, DDay, Dn, DpN, DInvalids, DInvalidsOut), % A.
	process_boundN_actions(DDay, DpDay, DpN, Dn, DInvalidsOut, DpInvalidsOut) % B.
%	process_DpDiffSets(DDay, DpDay, DpN, Dn,  DpInvalids, DpInvalidsOut) % B.
	),
	diff_insert(DAc, Dn, DAcOut), % [DAc|Dn]
	diff_insert(DpAc, DpN, DpAcOut), % [DpAc|DpN]
	updateDayPairsInvalidValues(D, Dp, DAcOut, DpAcOut, DpRecord, [DInvalidsOut|DpInvalidsOut], InvalidValues).
	%TODO fail actions
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 2 types of propagation techniques A, B, C (A, B are symetric)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% process_boundN_actions(+Dp, +D, +Dn, +DpN, +DInvalids, -DInvalidsOut) :-
% add incompatible domain values of D to DInvalids and returns in DInvalidsOut 
% Dp played day assignments ; D other day assignments
% DpN player assignment in played day player
% Dn player assgnment in other day player
process_boundN_actions([], [], _, _, [], []).
process_boundN_actions([DpI|Dp], [Di|D], Dn, DpN, [X|DInvalids], [Y|DInvalidsOut] ) :-
	( (ground(DpI), DpI == DpN, fd_var(Di)) ->  %played index is not var thus gonna fail 
	fdset_add_element(X, Dn, Y)
	;
	X=Y
	),
	process_boundN_actions(Dp, D, Dn, DpN, DInvalids, DInvalidsOut).
	

% process_unboundN_actions(Dp, D, DAc, DpN, DInvalids, DInvalidsOut) :-
% add action removing all incompatible values of Dn
process_unboundN_actions(Dp, D, DAc, DpN, DInvalids, DInvalidsOut) :-
	empty_fdset(E),
	get_Dn_invalid_values(Dp, D, DpN, E, DnDiffSet),
	set_Dn_DiffSet(DAc, DnDiffSet, DInvalids, DInvalidsOut).


% set_Dn_DiffSet(DAc, Q, DInvalids, DInvalidsOut) :-
set_Dn_DiffSet(E-E1, Q, [X|DInvalids], [Y|DInvalids]) :-
	unify_with_occurs_check(E, E1),
	fdset_union(X, Q, Y).
set_Dn_DiffSet([_|DAc]-E, Q, [X|DInvalids], [X|DInvalidsOut]) :-
	\+ unify_with_occurs_check([_|DAc], E),
	set_Dn_DiffSet(DAc-E, Q, DInvalids, DInvalidsOut).


% get_Dn_invalid_values(+Dp, +D, +DpN, +DiffSetIn, -DiffSetOut ) :-
% gets invalid sets for Dn 
get_Dn_invalid_values([], [], _, S, S).
get_Dn_invalid_values([DpI|Dp], [Di|D], DpN, DiffSetIn, DiffSetOut) :-
	( (ground(DpI), ground(Di), DpN =:= DpI) ->
	fdset_add_element(DiffSetIn, Di, DiffSetOutEn)
	;
	% jump over columns with at least one not grounded cell
	DiffSetOutEn = DiffSetIn
	),
	get_Dn_invalid_values(Dp, D,  DpN, DiffSetOutEn, DiffSetOut). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finding changes in variable assignments between pair_constrain calls
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% next_grounded_state(+Attendance, +PrevState, -NextState, -PlayedRecord) :-
% from current days Attandance and PrevState creates NextState and PlayedRecord
% if PrevState is [] only NextState is created
next_grounded_state([], [], [], []).
next_grounded_state([D|Attendance], [], [Dns|NextState], X) :-
	day_state(D, Dns),
	next_grounded_state(Attendance, [], NextState, X).
next_grounded_state([D|Attendance], [Dps|PrevState], [Dns|NextState], [NormalizedRecord|PlayedRecord]) :-
	day_state(D, Dns),
	played_record(Dps, Dns, Record),
	(
	none_record(Record) -> NormalizedRecord = none
	;
	NormalizedRecord = Record	
	),
	next_grounded_state(Attendance, PrevState, NextState, PlayedRecord).


% played_record(+Dps, +Dns, -Record) :-
% creates played record of values ground|unground|none from Dps previous state and Dns current state
played_record([], [], []).
played_record([ground|Dps], [ground|Dns], [none|Record]) :-
	played_record(Dps, Dns, Record).
played_record([ground|Dps], [var|Dns], [unground|Record]) :-
	throw(unground),
	played_record(Dps, Dns, Record).
played_record([var|Dps], [ground|Dns], [ground|Record]) :-
	played_record(Dps, Dns, Record).
played_record([var|Dps], [var|Dns], [none|Record]) :-
	played_record(Dps, Dns, Record).


% none_record(+Xs) :-
% if day played_record is list of none predicat succeed 
none_record([]).
none_record([none|Xs]) :-
	none_record(Xs).

% day_state(+D, -NextState) :-
% from current day D makes bitmap state ground|var which is returned in NextState
day_state([], []).
day_state([P|D], [var|NextState]) :- 
	fd_var(P),
	day_state(D, NextState).
day_state([P|D], [ground|NextState]) :- 
	ground(P),
	day_state(D, NextState).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Diff list hlepers 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% https://johnwickerson.wordpress.com/2009/01/22/implementing-difference-lists-in-prolog/
diff_cp(T-T1, Q-Q ) :- unify_with_occurs_check(T,T1).
diff_cp([N|Xs]-E, [N|Ys]-Q) :- \+ unify_with_occurs_check([N|Xs], E), diff_cp(Xs-E, Ys-Q).


diff_cat(X-Y, Y-YE, X-YE).

diff_catL(X-Y, Y, X).

diff_insert(X-Y, I, X-E) :- Y = [I|E].

diff_cp_cat(X, Y, Z) :-
	diff_cp(X, Q),
	diff_cat(Q, Y, Z).

diff_cp_catL(X, Y, Z) :-
	diff_cp(X, Q),
	diff_catL(Q, Y, Z).

diff_to_list(X-[], X).

list_to_diff([], E-E).
list_to_diff([X|Xs], [X|Ys]-E) :- list_to_diff(Xs, Ys-E).


