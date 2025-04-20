include "data.dzn";
include "globals.mzn";

int: n;
int: n3 = n div 3;

constraint n mod 3 == 0;

enum meals = { starter, main, dessert };

% assign meals: first third gets starter, middle gets dinner and final gets dessert
% can probably be made more random
function 1..n: determine_host(meals: meal, int: i) = 
  if meal == starter then           i
  else if meal == main then    n3 + i 
  else                       2*n3 + i
  endif endif;

% ideally the assignments should have been variably assigned as well, but we need 
% symmetry breaking anyway and this was a good way to do it while also allowing the 
% pairwise host constraint later (the global_cardinality constraint doesn't allow 
% for `array of var int` in its cover argument)
array[meals, 1..n3] of 1..n: hosts = [ 
  (meal, i): determine_host(meal, i) | 
  meal in meals, i in 1..n3 
];

% we channel the meal assignments (hosts) into a lookup table of which group hosts what
array[1..n] of var meals: host_meal;
constraint forall(meal in meals, i in hosts[meal, ..])(host_meal[i] = meal);

% this is what we want to find out
% each index represents a group containing a map of which hosts they will visit
array[1..n, meals] of var 1..n: routes;

constraint forall(i in 1..n)(
  all_different(routes[i, ..]) /\ % can't meet yourself or go to the same place twice
  routes[i, host_meal[i]] = i     % you must be at your own place when you host
);

% for each meal, exactly 3 groups must be assigned to each host
% this also ensures that no group can be assigned to a host that 
% doesn't exist for that meal
constraint forall(meal in meals)(
  global_cardinality(routes[.., meal], hosts[meal, ..], [3 | _ in 1..n3])
);

% ok buckle in

% we don't want any route between 2 hosts to be the same for any 2 groups (including 
% hosts). so if, say, group A has a starter -> main route of C -> D, then we don't 
% want group B to also have that route, since that would mean groups A and B meet at 
% both hosts C and D. this obviously also applies to main->dessert route, but also 
% the non-consecutive route of starter->dessert

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
  pairings[1, i] = (routes[i, starter] - 1) * n + routes[i, main]    /\
  pairings[2, i] = (routes[i, main]    - 1) * n + routes[i, dessert] /\
  pairings[3, i] = (routes[i, starter] - 1) * n + routes[i, dessert]
);

solve satisfy;

output [
  show2d(routes)
];
