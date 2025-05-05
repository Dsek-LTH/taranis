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

constraint all_different([hosts[m, i] | m in meals, i in 1..n3]);

% Possible guests
set of all_teams: possible_starter_guests = main_hosts union dessert_hosts;
set of all_teams: possible_main_guests = starter_hosts union dessert_hosts;
set of all_teams: possible_dessert_guests = starter_hosts union main_hosts;

% Each host invites 2 guests (use arrays instead of sets)
array[starter_hosts, 1..2] of var possible_starter_guests: starter_guests;
array[main_hosts, 1..2] of var possible_main_guests: main_guests;
array[dessert_hosts, 1..2] of var possible_dessert_guests: dessert_guests;

% Guests must be unique and ordered for each host
constraint forall(i in starter_hosts)(
    starter_guests[i, 1] < starter_guests[i, 2]
);
constraint forall(i in main_hosts)(
    main_guests[i, 1] < main_guests[i, 2]
);
constraint forall(i in dessert_hosts)(
    dessert_guests[i, 1] < dessert_guests[i, 2]
);

% Guests can only be at one host at a time (of course)
constraint forall(i in starter_hosts, j in starter_hosts where i != j, k in 1..2)(
    starter_guests[i, k] != starter_guests[j, k]
);
constraint forall(i in main_hosts, j in main_hosts where i != j, k in 1..2)(
    main_guests[i, k] != main_guests[j, k]
);
constraint forall(i in dessert_hosts, j in dessert_hosts where i != j, k in 1..2)(
    dessert_guests[i, k] != dessert_guests[j, k]
);

% Given a team, find out who is their host for each meal
array[all_teams] of var starter_hosts: starter_host_for;
array[all_teams] of var main_hosts: main_host_for;
array[all_teams] of var dessert_hosts: dessert_host_for;
constraint forall(s_h in starter_hosts)(
    starter_host_for[s_h] = s_h
);
constraint forall(s_h in starter_hosts, s_g in possible_starter_guests)(
    s_g == starter_guests[s_h, 1] \/
    s_g == starter_guests[s_h, 2] <->
    starter_host_for[s_g] = s_h
);
constraint forall(m_h in main_hosts)(
    main_host_for[m_h] = m_h
);
constraint forall(m_h in main_hosts, m_g in possible_main_guests)(
    m_g == main_guests[m_h, 1] \/
    m_g == main_guests[m_h, 2] <->
    main_host_for[m_g] = m_h
);
constraint forall(d_h in dessert_hosts)(
    dessert_host_for[d_h] = d_h
);
constraint forall(d_h in dessert_hosts, d_g in possible_dessert_guests)(
    d_g == dessert_guests[d_h, 1] \/
    d_g == dessert_guests[d_h, 2] <->
    dessert_host_for[d_g] = d_h
);

% the count of each host in starter_host_for must be equal to 3
% this is not needed for correctness, but it does seem to help the solver
constraint forall(s_h in starter_hosts)(
    count(starter_host_for, s_h) == 3
);
constraint forall(m_h in main_hosts)(
    count(main_host_for, m_h) == 3
);
constraint forall(d_h in dessert_hosts)(
    count(dessert_host_for, d_h) == 3
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
% team ids in the same outer group cannot meet
constraint forall(g in 1..gc)(
    forall(t1, t2 in outer_groups[g] where t1 < t2)(
        starter_host_for[t1] != starter_host_for[t2] /\
        main_host_for[t1] != main_host_for[t2] /\
        dessert_host_for[t1] != dessert_host_for[t2]
    )
);

solve :: int_search([starter_guests[h, g] | h in starter_hosts, g in 1..2] ++
               [main_guests[h, g] | h in main_hosts, g in 1..2] ++
               [dessert_guests[h, g] | h in dessert_hosts, g in 1..2],
               input_order, indomain_random, value_propagation)
      :: restart_linear(1) % ensure we don't get stuck
minimize worst_case;

output [
    "Routes: ", show2d(array2d(1..n, 1..1, [ % a bit hacky, but works
        [starter_host_for[i], main_host_for[i], dessert_host_for[i]]
        | i in all_teams
    ])), "\n",
    "worst_case = ", show(worst_case), "\n",
    "best_case = ", show(best_case), "\n",
    "total_distance = ", show(total_distance), "\n",
    % "starter_host_for = ", show(starter_host_for), "\n",
    % "main_host_for = ", show(main_host_for), "\n",
    % "dessert_host_for = ", show(dessert_host_for), "\n",
    % "starter_guests = ", show2d(starter_guests), "\n",
    % "main_guests = ", show2d(main_guests), "\n",
    % "dessert_guests = ", show2d(dessert_guests)
];