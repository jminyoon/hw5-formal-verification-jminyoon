class LimitedStack {

   var arr : array<int>    // contents
   var capacity : int   // max number of elements in stack.
   var top : int       // The index of the top of the stack, or -1 if the stack is empty.
   var counter: int

   predicate isValid() //Predicate = function that returns bool.
      reads this
   {
      && arr != null
      && arr.Length > 0
      && 0 < capacity <= arr.Length
      && -1 <= top < capacity
   }

   predicate isEmpty()
      reads this
      reads arr
   {
      && (forall i | 0 <= i < arr.Length :: arr[i] == 0)
      && top == -1
   }

   predicate isFull()
      reads this
   {
      top == capacity - 1
   }

   method Init(c : int)
      modifies this
      requires 
         && c > 0
      ensures 
         && fresh(arr)
         && isEmpty()
         && isValid()
         && capacity == c
   {
      capacity := c;
      arr := new int[c](i => 0);
      top := -1;
      counter := 0;
   } 

   method Peek() returns(x : int)
      modifies this
      requires
         && isValid()
         && !isEmpty()
   {
      x := 0;
      if(0 <= top < capacity) {
         x := arr[top];
      }
      return x;
   }

   method Pop() returns(x : int)
      modifies this
      requires
         && isValid()
         && !isEmpty()
   {
      x := 0;
      if(0 <= top < capacity) {
         x := arr[top];
      }
      LimitedStack.Shift();
      return x;
   }
   
   method Push(x : int)
      modifies this
      modifies arr
      requires
         && isValid()
         && !isFull()
      ensures
         && isValid()
         && top == old(top) + 1
         && top >= 0
         && arr[top] == x
   {
      arr[top + 1] := x;
      top := top + 1;
   }
      
   method Shift()
      requires 
         && isValid() 
         && !isEmpty()
      ensures 
         && isValid()
         && forall i : int :: 0 <= i < capacity - 1 ==> arr[i] == old(arr[i + 1])
         && top == old(top) - 1
      modifies this.arr, this`top
   {
      var i : int := 0;
      while (i < capacity - 1 )
         invariant 0 <= i < capacity
         invariant top == old(top)
         invariant forall j : int :: 0 <= j < i ==> arr[j] == old(arr[j + 1])
         invariant forall j : int :: i <= j < capacity ==> arr[j] == old(arr[j])
      {
         arr[i] := arr[i + 1];
         i := i + 1;
      }
      
      top := top - 1;
   }
   method Main(){
      var s := new LimitedStack;
      s.Init(3);

      assert s.isEmpty() && !s.isFull();

      //s.Push(27);
      //assert !s.Empty();

      //var e := s.Pop();
      //assert e == 27;

      //s.Push(5);
      //s.Push(32);
      //s.Push(9);
      //assert s.Full();

      //var e2 := s.Pop();
      //assert e2 == 9 && !s.Full();
      //assert s.arr[0] == 5;

      //s.Push(e2);
      //s.Push2(99);

      //var e3 := s.Peek();
      //assert e3 == 99;
      //assert s.arr[0] == 32;
   }
}
