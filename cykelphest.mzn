% include "data.dzn";
include "data_big.dzn";
include "globals.mzn";

int: n;
int: n3 = n div 3;
constraint n mod 3 == 0;

enum meals = { starter, main, dessert };
array[meals, 1..n3] of 1..n: hosts;

% we channel the meal assignments (hosts) into a lookup table of which group hosts what
array[1..n] of var meals: host_meal;
constraint forall(meal in meals, i in hosts[meal, ..])(host_meal[i] = meal);

% this is what we want to find out
% each index represents a group containing a map of which hosts they will visit
% so for example, if group 1 has a route of 1 -> 2 -> 3, then routes[1, main] = 2,
array[1..n, meals] of var 1..n: routes;

constraint forall(i in 1..n)(
  all_different(routes[i, ..]) /\ % can't go to the same place or host twice
  routes[i, host_meal[i]] = i     % you must be at your own place when you host
);

% for each meal, exactly 3 groups must be assigned to each host
% this also ensures that no group can be assigned to a host that doesn't exist for 
% that meal
constraint forall(meal in meals)(
  global_cardinality(
    routes[.., meal], % domain
    hosts[meal, ..],  % allowed values
    [3 | _ in 1..n3]  % allowed counts (always 3)
  )
);

% ok buckle up

% we don't want any route between 2 hosts to be the same for any 2 groups (including 
% hosts). so if, say, group A has a starter -> main route of C -> D, then we don't 
% want group B to also have that route, since that would mean groups A and B meet at 
% both hosts C and D. this obviously also applies to the main -> dessert route, but 
% also the non-consecutive route of starter -> dessert

% tracking each pair as-is requires minizinc to keep track of a ton of disjunctions, 
% which is *really* expensive (pretty much unsolvable for n > 15), so to make this 
% efficient we can map each pair of number to a unique number in the range 1..n*n by 
% using the formula (x-1)*n + y. 

% this allows us to use a single array to keep track of the pairs (for one type of 
% pair, e.g starter -> main), which *then* allows us to use alldifferent (which is 
% hyper optimized) to ensure that no two groups have the same pair.
% and then we combine all types of pairs into a 2d array
array[1..3, 1..n] of var 1..n*n: pairings;
constraint forall(i in 1..3)(alldifferent(pairings[i, ..]));
constraint forall(i in 1..n)(
  pairings[1, i] = (routes[i, starter] - 1) * n + routes[i,    main] /\
  pairings[2, i] = (routes[i,    main] - 1) * n + routes[i, dessert] /\
  pairings[3, i] = (routes[i, starter] - 1) * n + routes[i, dessert]
);


% we calculate all meetings between different groups in the form
% group -> { all groups that meet with this group at some point }
array[1..n] of var set of 1..n: meetings;
constraint forall(i, k in 1..n)(meetup(i, k) <-> k in meetings[i]);
predicate meetup(int: i, int: k) = 
  exists(meal in meals)(routes[i, meal] == routes[k, meal]);

% outer groups: see datafile
int: gc;
array[1..gc] of set of 1..n: outer_groups;
constraint all_disjoint(outer_groups);

% lookup table to find out which group a host belongs to
array[1..n] of var opt 0..gc: group_lookup;
constraint forall(i in 1..n, g in 1..gc)(i in outer_groups[g] -> group_lookup[i] = g);

% if two groups are in the same outer group, they can't meet
constraint forall(i, k in 1..n where i < k)(
  group_lookup[i] = group_lookup[k] -> not (k in meetings[i]) % this is wild 
);

solve satisfy;

output [
  show(meetings), "\n", 
  show2d(routes), "\n", 
  % show(group_lookup)
];