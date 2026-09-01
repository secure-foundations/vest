# Mutual recursion design notes

```ts
generator = λfuncsTuple ->
  let (recEven, recOdd) = funcsTuple in
  
  (
    λn -> if n == 0 then true  else recOdd(n - 1),  // The even logic
    λn -> if n == 0 then false else recEven(n - 1)  // The odd logic
  )

recursiveTuple = fix(generator)
    
let (isEven, isOdd) = recursiveTuple

isEven(4)
isOdd(3)
```


```ts
type Request = EvenReq(Int) | OddReq(Int)

generator = λrecFunc -> λrequest ->
  match request with
  | EvenReq(n) -> 
      if n == 0 then true  
      else recFunc(OddReq(n - 1))  // Mutually recursive call via sum tag
      
  | OddReq(n) -> 
      if n == 0 then false 
      else recFunc(EvenReq(n - 1)) // Mutually recursive call via sum tag

unifiedFunc = fix(generator)

isEven = λn -> unifiedFunc(EvenReq(n))
isOdd  = λn -> unifiedFunc(OddReq(n))

isEven(4)
isOdd(3)
```
