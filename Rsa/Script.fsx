// Learn more about F# at http://fsharp.net. See the 'F# Tutorial' project
// for more guidance on F# programming.

open System
open System.Collections
open System.Numerics

let random = Random()

let rec randomNumber (minInclusive : bigint) (maxInclusive : bigint) =
  let bytes = maxInclusive.ToByteArray()
  random.NextBytes bytes
  bytes.[bytes.Length-1] <- bytes.[bytes.Length-1] &&& 127uy // force to be positive
  let nr = BigInteger(bytes)
  if nr >= minInclusive && nr <= maxInclusive then nr else randomNumber minInclusive maxInclusive

let powMod a m n = // a^m (mod n)
  let rec calc M y z =
    if M % 2I = 0I then
      calc (m/2I) y ((z*z) % n)
    else
      let y' = (z * y) % n
      if m = 0I then y'
      else calc (m/2I) y' ((z*z) % n)
  calc m 1I a
  
let millerRabinPrimeTest n k =
  let d,s =
    let rec factor s d =
      if d % 2I = 1I then s,d
      else factor (s+1I) (d/2I)
    factor 0I (n-1I)

  let rec witnessLoop iteration =
    if iteration < k then
      let a = randomNumber 2I (n-2I)
      let x = powMod a d n
      if x = 1I || x = n - 1I then
        witnessLoop (iteration + 1)
      else
        let isComposite =      
          ((seq { 1I .. s - 1I }
          |> Seq.scan (fun x' _ -> powMod x' 2I n) x
          |> Seq.tryPick (fun x' -> if   x' = 1I     then Some true
                                    elif x' = n - 1I then Some false
                                    else None))
          |> defaultArg) true
        if isComposite then false else witnessLoop (iteration+1)
    else
      true
  witnessLoop 0
         
millerRabinPrimeTest 1234567I 50

for i in 5I .. 10000I do
  printf "%A = %A" i (millerRabinPrimeTest i 50)

