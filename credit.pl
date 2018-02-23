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
	group_size_satisfy(DaysAttendance, G, K),
	pair_constrain(DaysAttendance),
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

pair_constrain(P) :-
	suspensions(P, Suspensions),
	fd_global(pair_constrain(P), empty, Suspensions).
	
				     
suspensions([], []).
suspensions([D|DaysAttendance], Suspensions) :-
	suspensions_day(D, Suspensions, SLast),
	suspensions(DaysAttendance, SLast).

suspensions_day([], SLast, SLast).
suspensions_day([P|Attendance], [val(P)|Suspensions], SLast) :-
	suspensions_day(Attendance, Suspensions, SLast).

:- use_module(library(avl)).

:- multifile clpfd:dispatch_global/4.
clpfd:dispatch_global(pair_constrain(P), Sin, Sout, Actions) :-
	next_grounded_state(P, Sin, Sout),
	invalidateDomains(P, Sout, InvalidValues),
	gather_actions(P, InvalidValues, Actions).



% gather_actions(+Attandance, +InvalidValues, -Actions) :-
gather_actions([], [], []).
gather_actions([D|Attandance], [DInvalids|InvalidValues], Actions) :-
	gather_day_actions(D, DInvalids, Actions, LastAction),
	gather_actions(Attandance, InvalidValues, LastAction).


% gather_day_actions(D, DInvalids, Actions, LastAction) :-
gather_day_actions([], [], Actions, Actions).
gather_day_actions([P|D], [InvalidSet|DInvalids], [P in_set ReducedSet|Actions], LastAction) :-
	(empty_fdset(InvalidSet) -> true
	;
	fd_set(P, X),
	fdset_subtract(X, InvalidSet, ReducedSet) 
	),
	gather_day_actions(D, DInvalids, Actions, LastAction).


init_DaysDiffSets([], []).
init_DaysDiffSets([D|AttandanceDays], [X|Xs]) :-
	init_DpDiffSets(D, X),
	init_DaysDiffSets(AttandanceDays, Xs).

init_DpDiffSets([], []).
init_DpDiffSets([_|D], [X|Xs]) :-
	empty_fdset(X),
	init_DpDiffSets(D, Xs).


% invalidateDomains(+AttendanceDays, +PlayedRecord, -InvalidValues) :-
invalidateDomains(AttendanceDays, PlayedRecord, InvalidValues) :-
	init_DaysDiffSets(AttendanceDays, InvalidValuesIn),
	invalidateDomainsLoop(AttendanceDays, [], PlayedRecord, [], InvalidValuesIn, InvalidValues).


% invalidateDomainsLoop(+AttendanceDays, []PairDays, +PlayedRecord, []PairsInvalidsBegin, +PairsInvalidEnd, -InvalidValues) :-
% loop over AttandanceDays and update DayPairsInvalidValues if day was played
invalidateDomainsLoop([], _, [], Begin, End, [Begin|End]).
invalidateDomainsLoop([D|AttendanceDays], PairDays, [none|PlayedRecord], PairsInvalidsBegin, [DpInvalids|PairsInvalidEnd], InvalidValues) :-
	% skip not played days
	invalidateDomainsLoop(AttendanceDays, [PairDays|D], PlayedRecord, [PairsInvalidsBegin|DpInvalids], PairsInvalidEnd, InvalidValues).
invalidateDomainsLoop([Dp|AttendanceDays], PairDays, [DpRecord|PlayedRecord], PairsInvalidsBegin, [DpInvalids|PairsInvalidEnd], InvalidValues) :-
	DpRecord \= none,
	invalidatePairs([PairDays|AttendanceDays], Dp, DpRecord, PairsInvalidsBegin, DpInvalids, PairsInvalidEnd, PairsInvalidsBeginOut, DpInvalidsOut, PairsInvalidEndOut),
	invalidateDomainsLoop(AttendanceDays, [PairDays|Dp], PlayedRecord, [PairsInvalidsBeginOut|DpInvalidsOut], PairsInvalidEndOut, InvalidValues).

invalidatePairs([], _, _, [], I, [], [], I, []).
invalidatePairs([D|PairDays], Dp, DpRecord, [DInvalids|PairsInvalidsBegin], DpInvalids, PairsInvalidEnd, [DInvalidsOut|PairsInvalidsBeginOut], DpInvalidsOut, PairsInvalidEndOut) :-
	% D days befor Dp
	updateDayPairsInvalidValues(D, Dp, [], [], DpRecord, [DInvalids|DpInvalids], [DInvalidsOut|DpInvalidsOutX]),
	invalidatePairs(PairDays, Dp, DpRecord, PairsInvalidsBegin, DpInvalidsOutX, PairsInvalidEnd, PairsInvalidsBeginOut, DpInvalidsOut, PairsInvalidEndOut).
invalidatePairs([D|PairDays], Dp, DpRecord, [], DpInvalids, [DInvalids|PairsInvalidEnd], [], DpInvalidsOut, [DInvalidsOut|PairsInvalidEndOut]) :-
	% D days after Dp
	updateDayPairsInvalidValues(D, Dp, [], [], DpRecord, [DInvalids|DpInvalids], [DInvalidsOut|DpInvalidsOutX]),
	invalidatePairs(PairDays, Dp, DpRecord, [], DpInvalidsOutX, PairsInvalidEnd, _, DpInvalidsOut, PairsInvalidEndOut).
	

% updateDayPairsInvalidValues(+D, +Dp, []DAc, []DpAc, +DpRecord, +InvalidValuesIn, +InvalidValues) :- 
% for each player selected in DpRecord invalid values computation is done
% D other day to process
% Dp played day to process
% DAc processed players acumulator
% DpAc processed played players acumulator
% DpRecord bit map determinig if player was played (none vs hit)
% InvalidsValuesIn = [DInvalids|DpInvalids] so far gathered invalids for D resp. Dp days
% InvalidsValuesOut = [DInvalidsOut|DpInvalidsOut] updated invalids for D resp. Dp days
updateDayPairsInvalidValues([], [], _, _, [], X, X).
updateDayPairsInvalidValues([Di|D], [DpI|Dp], DAc, DpAc, [none|DpRecord], InvalidValuesIn, InvalidValues) :- 
	%skip not played players
	updateDayPairsInvalidValues(D, Dp, [DAc|Di], [DpAc|DpI], DpRecord, InvalidValuesIn, InvalidValues).
updateDayPairsInvalidValues([Dn|D],  [DpN|Dp], DAc, DpAc, [hit|DpRecord], [DInvalids|DpInvalids], InvalidValues) :- 
	DDay = [DAc|[Dn|D]],
	DpDay = [DpAc|[DpN|Dp]],
	(fd_var(Dn) -> process_unboundN_actions([DpAc|[none|Dp]], DDay, Dn, DpN, DInvalids, DInvalidsOut), % C.
	DpInvalidsOut = DpInvalids
	;
	process_boundN_actions(DpDay, DDay, Dn, DpN, DInvalids, DInvalidsOut), % A.
	process_DpDiffSets(DDay, DpDay, DpN, Dn,  DpInvalids, DpInvalidsOut) % B.
	),
	%TODO fail actions
	updateDayPairsInvalidValues(D, Dp, [DAc|Dn], [DpAc|DpN], DpRecord, [DInvalidsOut|DpInvalidsOut], InvalidValues).

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


% process_boundN_actions(+Dp, +D, +Dn, +DpN, +DInvalids, -DInvalidsOut) :-
% add incompatible domain values of D to DInvalids and returns in DInvalidsOut 
% Dp played day assignments ; D other day assignments
% DpN player assignment in played day player
% Dn player assgnment in other day player
process_boundN_actions([], [], _, _, [], []).
process_boundN_actions([DpI|Dp], [Di|D], Dn, DpN, [X|DInvalids], [X|DInvalidsOut] ) :- %skip
	(fd_var(DpI); DpI =\= DpN; ground(Di)), 
	process_boundN_actions(Dp, D, Dn, DpN, DInvalids, DInvalidsOut).
process_boundN_actions([DpI|Dp], [Di|D], Dn, DpN, [X|DInvalids], [Y|DInvalidsOut] ) :-
	ground(DpI), DpI =:= DpN, fd_var(Di), %played index is not var thus gonna fail 
	fdset_add_element(X, Dn, Y),
	process_boundN_actions(Dp, D, Dn, DpN, DInvalids, DInvalidsOut).
	
% process_DpDiffSets(+D, +Dp, +DpN, +Dn,  +DpDiffSets, -DpDiffSetsOut) :-
% adds to DpDiffSets incompatible values
process_DpDiffSets([], [], _, _, [], []).
process_DpDiffSets([DpI|Dp], [Di|D], Dn, DpN, [X|DpDiffSets], [X|DpDiffSetsOut]) :- %skip
	(fd_var(Di); Di =\= Dn; ground(DpI)), 
	process_DpDiffSets(Dp, D, Dn, DpN, DpDiffSets, DpDiffSetsOut).
process_DpDiffSets([DpI|Dp], [Di|D], Dn, DpN, [DpIDS|DpDiffSets], [DpIDSOut|DpDiffSetsOut]) :-
	ground(Di), Di =:= Dn, fd_var(DpI), %played index is not var thus gonna fail
	fdset_add_element(DpIDS, DpN, DpIDSOut),
	process_DpDiffSets(Dp, D, Dn, DpN, DpDiffSets, DpDiffSetsOut).


% process_unboundN_actions(Dp, D, Dn, DpN, DInvalids, DInvalidsOut) :-
% add action removing all incompatible values of Dn
process_unboundN_actions(Dp, D, DpN, DInvalids, DInvalidsOut) :-
	empty_fdset(E),
	get_Dn_invalid_values(Dp, D, DpN, E, DnDiffSet, DInvalids, DInvalidsOut, X-Y),
	fdset_union(DnDiffSet, X, Y).


% get_Dn_invalid_values(+Dp, +D, +DpN, +DiffSetIn, -DiffSetOut, +DInvalids, -DInvalidsOut, -X-Y) :-
% gets invalid sets for Dn and subsequently updates DInvalidsOut and unifies Y as placeholder for (X union invalids)
get_Dn_invalid_values([], [], _, S, S, [], [], _).
get_Dn_invalid_values([none|Dp], [_|D], DpN, DiffSetIn, DiffSetOut, [X|DInvalids], [Y|DInvalidsOut], X-Y) :-
	% jump over played column 
	get_Dn_invalid_values(Dp, D,  DpN, DiffSetIn, DiffSetOut, [X|DInvalids], [X|DInvalidsOut], _). 
get_Dn_invalid_values([DpI|Dp], [Di|D], DpN, DiffSetIn, DiffSetOut, [X|DInvalids], [X|DInvalidsOut], Y) :-
	% jump over columns with at least one not grounded cell
	(fd_var(DpI); fd_var(Di)),
	get_Dn_invalid_values(Dp, D,  DpN, DiffSetIn, DiffSetOut, DInvalids, DInvalidsOut, Y). 
get_Dn_invalid_values([DpI|Dp], [Di|D], DpN, DiffSetIn, DiffSetOut, [X|DInvalids], [X|DInvalidsOut], Y) :-
	ground(DpI), ground(Di), DpN =:= DpI,
	fdset_add_element(DiffSetIn, Di, DiffSetOutEn),
	get_Dn_invalid_values(Dp, D,  DpN, DiffSetOutEn, DiffSetOut, DInvalids, DInvalidsOut, Y). 


	
% FOLLOWS FINDING OF READY GROUNDED 

% next_grounded_state(Attendance, PrevState, NextState) :-
next_grounded_state([], [], []).
next_grounded_state([D|Attendance], [Dps|PrevState], [Dns|NextState]) :-
	day_state(D, Dps, DnsX),
	normalize_state(DnsX, [], Dns),
	next_grounded_state(Attendance, PrevState, NextState).

normalize_state([], none).
normalize_state([none|Xs], Ac, Res) :-
	normalize_state(Xs, [Ac|none], Res).
normalize_state([grounded|Xs], Ac, [Ac|[grounded|Xs]]).
normalize_state([ungrounded|Xs], Ac, [Ac|[grounded|Xs]]).

% day_state(+D, +Dps, -NextState) :- 
day_state([], [], []).
day_state([P|D], [grounded|Dps], [ungrounded|NextState]) :- 
	fd_var(P),
	throw(ungrounded),
	day_state(D, Dps, NextState).
day_state([P|D], [grounded|Dps], [none|NextState]) :- 
	ground(P),
	day_state(D, Dps, NextState).
day_state([P|D], [ungrounded|Dps], [grounded|NextState]) :- 
	ground(P),
	day_state(D, Dps, NextState).
day_state([P|D], [ungrounded|Dps], [none|NextState]) :- 
	fd_var(P),
	day_state(D, Dps, NextState).

