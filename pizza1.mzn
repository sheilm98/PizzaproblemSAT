% Use this editor as a MiniZinc scratch book
%Pizza problem

%Minimize goal: obtain all the ordered pizzas for the least possible cost. Not all vouchers
% need to be used, and a voucher/coupon does not need to be totally used


%input variables from data file
int: n;   %number of pizzas to obtain
set of int: Pizzas = 1 .. n; % just to make code easier to write
array[Pizzas] of int: price;  % price is array of n pizza prices (unary mapping)
int: m;   %number of coupons/vouchers
set of int: coupons = 1..m;
array[coupons] of int: buy; 
array[coupons] of int: free;

array[coupons,Pizzas] of var bool: Apply;
array[coupons,Pizzas] of var bool: Justify;

var set of Pizzas: Paid;
var set of coupons: Used; 


%final sum
var int: cost = sum (i in Pizzas) (bool2int(i in Paid) * price[i]);


%%constraints


% 1. pay for exactly the pizzas that we don't get by using the coupons
constraint forall(p in Pizzas)((p in Paid) <-> not exists(c in Used)(Apply[c,p]));

% 2. used is the set of applied coupons
constraint forall(c in coupons)((c in Used) <-> exists(p in Pizzas)(Apply[c,p]));

% 3. Any coupon that is used must be Justified by enough paid pizzas
constraint forall(c in coupons) ((c in Used) -> sum(p in Pizzas)(bool2int(Justify[c,p] )) >=buy[c]);

% 4. No coupon is used for too many pizzas
constraint forall(c in coupons)((c in Used) -> (sum(p in Pizzas)(bool2int(Apply[c,p])) <= free[c]));

% 5. Each free pizza costs at most as much as the cheapest pizza used to justify the coupon used
constraint
  forall(c in coupons) (
      forall (p,q in Pizzas where p !=q) (
                ((Apply[c,p] /\ Justify[c,q]) -> (price[p] <= price[q])) 
                ));
                
% 6. We pay for all pizzas that justify using coupons
constraint forall (p in Pizzas)(
    forall(c in coupons) (
        Justify[c,p] -> (p in Paid)));

% 7. The total cost is not too large (total of all pizzas)
constraint cost <= sum(p in Pizzas)(price[p]);

% 8. Justify and apply hold only coupon-pizza pairs
constraint forall(c in coupons) (
    forall(p in Pizzas) (
      (Justify[c,p]) -> (
         ((1 <= c ) /\ (c<=m)) /\ ((1 <= p) /\ (p<=n)))
    ));

%9. Any pizza used to justify a coupon can only be used once
constraint forall(c in coupons) (
  forall(p in Pizzas)
    (Justify[c,p] -> not exists(v in coupons where c != v)(Justify[v,p])
));
            
%constraint forall(c in coupons) (
%    forall(p in Pizzas) (
%      (Apply[c,p]) -> (
%         ((1 <= c ) /\ (c<=m)) /\ ((1 <= p) /\ (p<=n)))
%    ));  
   

solve minimize cost;
output ["Paid: " ++ show(Paid)
    ++ "\nUsed" ++ show(Used) ++"\n"
    ++"Vouchers" ++ show(coupons) ++ "\n"]
    ++ 
    ["cost(" ++ show(cost)++")"];