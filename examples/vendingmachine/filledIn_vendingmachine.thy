theory filledIn_vendingmachine
imports 
Main 

begin 

record SS1 = 
STOCK :: nat
TAKINGS :: nat

locale zmathlang_vm = 
fixes stock :: "nat"
and takings :: "nat"
begin

definition PRE1 :: 
 "nat => bool"
where 
"PRE1 cash_tendered = (cash_tendered = price) "

definition PRE2 :: 
 "nat => bool"
where 
"PRE2 cash_tendered = (cash_tendered < price) "

definition CS0 :: 
"SS1 => SS1 => nat => nat => nat => bool"
where 
"CS0 vmstate vmstate' cash_tendered cash_refunded bars_delivered == True"

definition PRE3 :: 
" bool"
where 
"PRE3  = (stock > 0) "

definition CS2 :: 
 "SS1 => nat => SS1 => nat => nat => bool"
where 
"CS2 vmstate bars_delivered vmstate' cash_tendered cash_refunded == ((
(stock' = stock) 
\<and> (bars_delivered = 0) 
\<and> (cash_refunded = cash_tendered) 
\<and> (takings' = takings)))"

lemma TS2: 
"(PRE2 cash_tendered)
 <and>
 (CS2 vmstate bars_delivered vmstate' cash_tendered cash_refunded)
"
sorry

definition CS1 :: 
 "SS1 => nat => SS1 => nat => nat => bool"
where 
"CS1 vmstate bars_delivered vmstate' cash_tendered cash_refunded == ((
(stock' = stock - 1) 
\<and> (bars_delivered = 1) 
\<and> (cash_refunded = cash_tendered - price) 
\<and> (takings' = takings + price)))"

lemma TS1: 
"(PRE1 cash_tendered)
 <and>
 (PRE3 )
 <and>
 (CS1 vmstate bars_delivered vmstate' cash_tendered cash_refunded)
"
sorry

lemma TS3: 
"(TS1 cash_tendered vmstate bars_delivered vmstate' cash_refunded)
 <or>
 (TS2 cash_tendered vmstate bars_delivered vmstate' cash_refunded)
"
sorry

end
end
