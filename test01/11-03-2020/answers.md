# 11-03-2020

## Question 1

**Which of the following Hoare triples is FALSE?**

**a.** {true} skip {x ≥ 0}  
**b.** {x ≥ 0} x := x + 1 {x ≥ 0}  
**c.** {x ≠ 0} if x > 0 then y := 1 else y := -1 { x × y  > 0}  
**d.** {true} while i > 0 do i := i - 1 {i ≤ 0}  

**Answer:** A  

## Question 2

**Which of the following Hoare triples is FALSE?**
[Hint: In case of doubt, calculate the weakest precondition.]

**a.** {x > 0} x := z - x; y := z - x {y > 0}  
**b.** {x < y} x := z - x; y := z - y {x > y}  
**c.** {x > 0} x :=  x + y; y := x - y {y > 0}   
**d.** {x > 0} z := 1; y := x - z {y > 0}   

**Answer:** D   


## Question 3

**Which of the following expressions gives or is equivalent to the weakest precondition of the following Hoare triple?**
   ```
   {wp} while   x > y do x := x - y  {true}
   ```

**a.** y > 0      
**b.** x ≤ y ∨ y > 0   
**c.** x ≤ y ∧ y > 0     
**d.** x ≤ y     

**Answer:** B 


