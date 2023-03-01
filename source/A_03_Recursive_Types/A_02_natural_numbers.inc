***************
Natural Numbers
***************

.. code-block:: lean

  #check nat
  
  /-
  inductive nat
  | zero : nat
  | succ (n : nat) : nat
  -/
  
  -- notations for writing succ applications
  def three  := nat.zero.succ.succ.succ
  def three'  := (nat.succ(nat.succ(nat.succ(nat.zero))))
  
  
  -- increment is just succ application 
  def inc (n' : nat) : nat := n'.succ
  def three'' := inc(inc(inc nat.zero))
  
  def pred' : nat → nat :=
  begin
  assume n,
  cases n,
  exact 0,
  exact n,
  end 
  
  #eval pred' 6
  
  def pred : nat → nat 
  | nat.zero := nat.zero
  | (nat.succ n') := n' 
  
  #eval pred 5
  
  def sub2 : nat → nat 
  | nat.zero := nat.zero
  | (nat.succ nat.zero) := nat.zero
  | (nat.succ (nat.succ n')) := n'
  

