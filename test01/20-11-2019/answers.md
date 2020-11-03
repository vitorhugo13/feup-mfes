# 20-11-2019

## Question 1

**Which of the following Hoare triples is FALSE?**

**a.** {true} skip {false}   
**b.** {i < 0} while i < 0 do i := i + 1 {i = 0}  
**c.** {true} if x ≥ 0 then y := 1 else y := -1 {x * y ≥ 0}  
**d.** {x > 1} x := x - 1 {x > 0}   

**Answer:** A    

## Question 2  

**Which of the following Hoare triples is TRUE?**  

**a.** {y < 0} x :=  x + y; y := x - y {y > x}   
**b.** {true} z := x; y := z - 1 {y > x}   
**c.** {true} z := 1; y := x - z {x < y}  
**d.** {true} y := x; y := x + x + y {y > x}  

**Answer:** D  

## Question 3

**Which of the following expressions gives the weakest precondition of the following Hoare triple?**  
``` {wp} while r >= d  do r := r - d {0 ≤ r ∧ r < d} ```

**a.** r >= 0 ∧ d > 0  
**b.** r >= 0 \/ d > 0  
**c.** r >= 0  
**d.** d > 0  

**Answer:**  A
