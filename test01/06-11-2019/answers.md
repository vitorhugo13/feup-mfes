# 06-11-2019

## Question 1

**Which of the following Hoare triples is FALSE?**

**a.** {x > 2} skip {x > 1}  
**b.** {true} if x ≥ 0 then y := x else y := -x {y > 0}  
**c.** {x > 1} x := x + 1 {x > 2}  
**d.** {i > 0} while i > 0 do i := i - 1 {i = 0}  

**Answer:** B
**Justification:** to prove that a Hoare triple is false, just find a counter example.  
E.g: if x = 0, y will be 0 and it's not > 0.

## Question 2

**Which of the following Hoare triples is FALSE?**
[Hint: In case of doubt, calculate the weakest precondition.]

**a.** {true} y := x; y := x + x + y {y = 3x}  
**b.** {y > 1} z := x; y := y - z {x > y}  
**c.** {x > 1} z := 1; y := x - z {x > y}  
**d.** {x > 0} x :=  x + y; y := x - y {y > 0}  

**Answer:** B
**Justification:** to prove that a Hoare triple is false, just find a counter example.  
E.g: if x < 0, y will be > x.  


## Question 3

**Which of the following expressions gives or is equivalent to the weakest precondition of the following Hoare triple?**
   ```
   {wp} if a > b then x := a else x := b {x > 0}
   ```
[Hint: the given conditional statement is equivalent to x := max(a, b).]

**a.** x > 0  
**b.** a > 0 ∨ b > 0  
**c.** a > 0 ∧ b > 0  
**d.** true  

**Answer:** B
**Justification:** ``` wp(if C then S else T, Q)  =  C ∧ wp(S,Q) ∨  ¬C ∧ wp(T,Q)``` = a > 0 ∨ b > 0

## Question 4
### 4.a) Weakest preconditions
 ```
 1:  {x ≥ 0}     
 2:  **{x = x ∧ x ≥ 0}**    
 3:  z := x;  
 4:  **{z = x ∧ z ≥ 0}**  
 5:  y := 0;   
 6:  {z + y = x ∧ z ≥ 0}  // I   
 7:  while z ≠ 0 do   
 8:        {z ≠ 0 ∧  z + y = x ∧ z ≥ 0 ∧ z = V0}  // C ∧ I ∧ V = V0  
 9:        **{z-1+y+1 = x ∧ z-1 ≥ 0 ∧ 0 ≤ z-1 < V0}**      
10:        y := y+1;  
11:        **{z-1+y = x ∧ z-1 ≥ 0 ∧ 0 ≤ z-1 < V0}**   
12:        z := z−1  
13:        {z + y = x ∧ z ≥ 0 ∧ 0 ≤ z < V0}  // I ∧ 0 ≤ V < V0    
14:  {z = 0 ∧ z + y = x ∧ z ≥ 0}  // ¬ C ∧ I   
15:  {x = y}  
 ```
 
### 4.b) Implications 

* 1 ⇒ 2
x ≥ 0 ⇒ x = x ∧ x ≥ 0 
⇔ x ≥ 0 ⇒ x ≥ 0
⇔ true

* 8 ⇒ 9
z ≠ 0 ∧  z + y = x ∧ z ≥ 0 ∧ z = V0 ⇒ z-1+y+1 = x ∧ z-1 ≥ 0 ∧ 0 ≤ z-1 < V0
⇔ z > 0 ∧  z + y = x  ∧ z = V0 ⇒ z + y = x ∧ z ≥ 1 ∧ 0 ≤ z-1 < V0
⇔ z > 0 ∧  z + y = x  ∧ z = V0 ⇒ z + y = x ∧ z ≥ 1 ∧ 0 ≤ V0-1 < V0
⇔ z > 0 ∧  z + y = x  ∧ z = V0 ⇒ z + y = x ∧ z ≥ 1 ∧ true
⇔ true

* 14 ⇒ 15
z = 0 ∧ z + y = x ∧ z ≥ 0 ⇒ x = y
⇔ z = 0 ∧ x = y ⇒ x = y
⇔ true