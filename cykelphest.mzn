include "globals.mzn";
include "data_big.dzn";

int: n;
set of int: all_teams = 1..n;

int: n3 = n div 3;

enum meals = { starter, main, dessert };

constraint assert(n >= 9, "minimum 9 teams");
constraint assert((n) mod 3 == 0, "team count must be divisible by 3");

array[meals, 1..n3] of all_teams: hosts;

set of all_teams: starter_hosts = { hosts[starter, h] | h in 1..n3 };
set of all_teams: main_hosts = { hosts[main, h] | h in 1..n3 };
set of all_teams: dessert_hosts = { hosts[dessert, h] | h in 1..n3 };

constraint assert(
    card(starter_hosts) = n3 /\
    card(main_hosts) = n3 /\
    card(dessert_hosts) = n3, "all host groups must be of size n/3"
);
constraint all_disjoint([starter_hosts, main_hosts, dessert_hosts]);

% Only teams that doesn't host a starter meal can be invited to a starter meal, etc.
set of all_teams: possible_starter_guests = main_hosts union dessert_hosts;
set of all_teams: possible_main_guests = starter_hosts union dessert_hosts;
set of all_teams: possible_dessert_guests = starter_hosts union main_hosts;

% Which guests are invited to which host?
array[starter_hosts] of var set of possible_starter_guests: starter_guests;
array[main_hosts] of var set of possible_main_guests: main_guests;
array[dessert_hosts] of var set of possible_dessert_guests: dessert_guests;

% Each host gets exactly 2 guests
constraint forall(sh in starter_hosts)(
    card(starter_guests[sh]) = 2
);
constraint forall(mh in main_hosts)(
    card(main_guests[mh]) = 2
);
constraint forall(dh in dessert_hosts)(
    card(dessert_guests[dh]) = 2
);

constraint forall(sh in starter_hosts)(
    starter_guests[sh] subset possible_starter_guests
);
constraint forall(mh in main_hosts)(
    main_guests[mh] subset possible_main_guests
);
constraint forall(dh in dessert_hosts)(
    dessert_guests[dh] subset possible_dessert_guests
);

% Guests can only be at one host at a time (of course)
constraint all_disjoint(starter_guests);
constraint all_disjoint(main_guests);
constraint all_disjoint(dessert_guests);

% Collect all guest combinations and ensure they are all different
% This ensures that no two teams meet each other more than once
array[all_teams] of var set of all_teams: all_guest_combinations;
constraint all_different(all_guest_combinations);
% "fill in" the guest combinations
constraint forall(s_h in starter_hosts)(
    all_guest_combinations[s_h] = starter_guests[s_h]
);
constraint forall(m_h in main_hosts)(
    all_guest_combinations[m_h] = main_guests[m_h]
);
constraint forall(d_h in dessert_hosts)(
    all_guest_combinations[d_h] = dessert_guests[d_h]
);
% Symmetry breaking I guess?
constraint forall(i in 1..n3-1)(
    all_guest_combinations[i] < all_guest_combinations[i+1]
);

% Given a team, find out who is their host for each meal
array[all_teams] of var starter_hosts: starter_host_for;
array[all_teams] of var main_hosts: main_host_for;
array[all_teams] of var dessert_hosts: dessert_host_for;

constraint forall(i in all_teams) (
    if i in starter_hosts then
        starter_host_for[i] = i
    else
        exists(s_h in starter_hosts)(i in starter_guests[s_h] /\ starter_host_for[i] = s_h)
    endif
);
constraint forall(i in all_teams) (
    if i in main_hosts then
        main_host_for[i] = i
    else
        exists(m_h in main_hosts)(i in main_guests[m_h] /\ main_host_for[i] = m_h)
    endif
);
constraint forall(i in all_teams) (
    if i in dessert_hosts then
        dessert_host_for[i] = i
    else
        exists(d_h in dessert_hosts)(i in dessert_guests[d_h] /\ dessert_host_for[i] = d_h)
    endif
);

% (x, y) coordinates per host
% 10 000 is set to maximum, so we can allow MiniZinc compilers/solvers to use bounded variables 
array[all_teams, 1..2] of 0..10000: coordinates;
% -- Precalculate distances between hosts, rounded to nearest integer
array[all_teams, all_teams] of 0..10000: distance_lookup = 
    array2d(all_teams, all_teams, [
        round(sqrt(
            (coordinates[i,1] - coordinates[j,1])^2 +
            (coordinates[i,2] - coordinates[j,2])^2
        ))
        | i,j in all_teams
    ]);

% -- In worst case, the maximum a team has to travel is twice the maximum distance
% -- between any two hosts (i.e. the longest route)
int: longest_route = max([distance_lookup[i,j] | i,j in all_teams where i != j]) * 2;
int: shortest_route = min([distance_lookup[i,j] | i,j in all_teams where i != j]) * 2;
% -- Travel distances per team
array[all_teams] of var shortest_route..longest_route: travel_distances;

% -- Calculate travel distances for each team, the cost of the route
constraint forall(i in all_teams)(
    travel_distances[i] =
        distance_lookup[starter_host_for[i], main_host_for[i]] +
        distance_lookup[main_host_for[i], dessert_host_for[i]]
);

% -- Calculate total distance traveled for all groups
var shortest_route * n.. longest_route * n: total_distance = sum(i in all_teams)(travel_distances[i]);
var shortest_route * 2..longest_route * 2: worst_case = max([travel_distances[i] | i in all_teams]);
var shortest_route * 2..longest_route * 2: best_case = min([travel_distances[i] | i in all_teams]);

% outer groups: see datafile
int: gc;
array[1..gc] of set of all_teams: outer_groups;
constraint all_disjoint(outer_groups);
% team ids in the same outer group cannot meet
constraint forall(g in 1..gc)(
    forall(t1, t2 in outer_groups[g] where t1 < t2)(
        starter_host_for[t1] != starter_host_for[t2] /\
        main_host_for[t1] != main_host_for[t2] /\
        dessert_host_for[t1] != dessert_host_for[t2]
    )
);

solve :: seq_search([
    int_search(starter_host_for ++ main_host_for ++ dessert_host_for, input_order, indomain_random, value_propagation),
    set_search(all_guest_combinations, input_order, indomain_min)
]) minimize worst_case;

output [
    "Starter guests: ", show(starter_guests), "\n",
    "Main guests: ", show(main_guests), "\n",
    "Dessert guests: ", show(dessert_guests), "\n",
    "Routes: ", show2d(array2d(1..n, 1..1, [ % a bit hacky, but works
        [starter_host_for[i], main_host_for[i], dessert_host_for[i]]
        | i in all_teams
    ])), "\n",
    "Total distance: ", show(total_distance), "\n",
    "Worst case distance: ", show(worst_case), "\n",
    "Best case distance: ", show(best_case), "\n",
    "Distances per team: ", show(travel_distances), "\n",
    ];
