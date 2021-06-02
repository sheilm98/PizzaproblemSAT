%Pizza problem second implementation
% DEFINITIONS
%
% Initial Input
int: n;
array[1..n] of int: price;
int: m;
array[1..m] of int: buy;
array[1..m] of int: free;

var set of 1..n: Paid;
var set of 1..m: Used; 

array[1..m, 1..n] of var bool: Justify;
array[1..m, 1..n] of var bool: Apply;

% CONSTRAINTS

% 1. If we paid for a pizza p, then it cannot be in the set of free pizzas
constraint forall(p in 1..n)
            ((p in Paid)
            <->
            not exists(c in Used)(Apply[c, p]));

% 2. If coupon c is used, then it must get at least one free pizza p with it
constraint forall(c in 1..m)
            ((c in Used)
            <->
            exists(p in 1..n)(Apply[c, p]));

% 3. Any used coupon c must be justified by paying for exactly some pizzas p
constraint forall(c in 1..m)
            ((c in Used)
            ->
            sum(p in 1..n)(Justify[c, p]) >= buy[c]);

% 4. The number of free pizzas cannot be greater than what is possible by
%      using coupon c 
constraint forall(c in 1..m)
            ((c in Used) -> sum(p in 1..n)(Apply[c, p]) <= free[c]);

% 5. Each free pizza costs at most as much as the cheapest pizza used to justify the coupon used
constraint forall(c in 1..m)
            (forall(p1, p2 in 1..n where p1 != p2)
              ((Apply[c, p1] /\ Justify[c, p2])
                ->
                price[p1] <= price[p2]));

% 6. Two coupons c1, c2 cannot be justified by using the same paid pizza p
constraint forall(p in 1..n)
            (forall(c1, c2 in 1..m where c1 != c2)
              (Justify[c1, p]
              ->
              not (Justify[c2, p])));

% 7. We pay for every pizza p used to justify use of a coupon c
constraint forall(p in 1..n)
            (forall(c in 1..m)(Justify[c, p] -> (p in Paid)));

% 8. The pairs in Justifies can only be consisting of a
%      pair (c, p) for coupon c and a pizza p
constraint forall(c in 1..m)
            (forall(p in 1..n)
              (Justify[c, p]
               ->
              (c in 1..m /\ p in 1..n)));

% 9. The pairs in UsedFor can only be consisting of a
%      pair (c, p) for coupon c and a pizza p
constraint forall(c in 1..m)
            (forall(p in 1..n)
              (Apply[c,p]
               ->
              (c in 1..m /\ p in 1..n)));

% get the total cost so we minimize it later
int: total = sum(price);
var int: COST =(sum(p in 1..n)(bool2int(p in Paid) * price[p]));

% 10. The total cost ($k$, the sum of all paid pizzas) 
% must be less or equal the sum of all pizza prices (that was obtained from adding p costs up)
constraint COST <= total;


% 11. coupons are not used more than they exist, and pizzas are not more than reqd
constraint forall(c in 1..m) (
    forall(p in 1..n) (
      (Apply[c,p]) -> (
         ((1 <= c ) /\ (c<=m)) /\ ((1 <= p) /\ (p<=n)))
    ));  
   

solve minimize COST;

output [ "Paid = " ++ show(Paid) ++ "\n" ++
         "Used = " ++ show(Used) ++ "\n" ++
         "Justify = " ++ show(Justify) ++ "\n" ++
         "Apply = " ++ show(Apply) ++ "\n" ++
         "COST = " ++ show(COST) ];