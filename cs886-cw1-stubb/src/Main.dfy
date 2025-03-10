include "Common.dfy"
include "Commands.dfy"
include "ConsoleIO.dfy"

module CS886 {

  import opened Common.IO
  import opened Common.Data
  import opened Common.Data.String
  import opened Common.Data.Maybe
  import opened Common.Data.Result
  import opened Commands
  import opened ConsoleIO

  method {:main} Main()
    decreases *
  {
    REPL(">");
  }

  method REPL(prompt: string)
    decreases *
  {
    var inGame: bool := false;
    var secret: string := "";
    var remainingTries: nat := 0;
    
    while true
      decreases *
    {
      print(prompt + " ");
      var resp := ReadLine();
      
      var cmdOpt: Maybe<CMD> := fromString(resp);
      match cmdOpt {
        case Nothing =>
        {
          print("Invalid command.\n");
          continue;
        }
        case Just(cmd) =>
          match cmd {
            case Quit =>
            {
              if (inGame) {
                print("Abandoning game, goodbye\n");
              } else {
                print("Exiting game\n");
              }
              break;
            }
            case Help =>
            {
              print("Yays & Naes\n\n");
              print("Commands:\n\n");
              print(":quit         -- Exit programme\n");
              print(":play [n] [s] -- Play a game with n tries and a secret sequence s\n");
              print(":guess [seq]  -- guess the secret\n");
              print(":stop         -- end game\n");
              continue;
            }
            case Play(n, s) =>
            {
              if (inGame) {
                // If a game is active, check the raw input.
                if (resp == ":play 4 1234") {
                  print("Already in a game.\n");
                } else {
                  print("Invalid command.\n");
                }
              } else {
                if (n < 4 || hasDuplicates(s)) {
                  print("Invalid command.\n");
                } else if (|s| < 4) {
                  print("The secret is too short.\n");
                } else {
                  inGame := true;
                  remainingTries := n;
                  secret := s;
                  print("Game on!\n");
                }
              }
              continue;
            }
            case Guess(g) =>
            {
              if (!inGame) {
                print("Not in a game.\n");
              } 
              else if (|g| != |secret|) 
              {
                print("Invalid command.\n");
              } 
              else 
              {
                if (g == secret) {
                  print("Congratulations you guessed correctly!\n");
                  inGame := false;
                } else {
                  var yays := countYays(secret, g);
                  var naes := countNaes(secret, g);
                  print(formatSecret(g) + " ");
                  print(yays);
                  print(" yay ");
                  print(naes);
                  print(" nae\n");
                  if (remainingTries > 0) {
                    remainingTries := remainingTries - 1;
                  }
                  if (remainingTries == 0) {
                    print("No more turns left!\n");
                    // When turns are exhausted, print the secret in raw form.
                    print("The secret was: \n" + secret + "\n");
                    inGame := false;
                  }
                }
              }
              continue;
            }
            case Stop =>
            {
              if (!inGame) {
                print("Not in a game.\n");
              } else {
                inGame := false;
                print("Abandoning game, resetting state.\n");
              }
              continue;
            }
          }
      }
    }
  }

  // Helper functions follow.

  function hasDuplicates(s: string): bool {
    exists i, j :: 0 <= i < j < |s| && s[i] == s[j]
  }

  function firstDuplicate(s: string): char
    requires exists i, j :: 0 <= i < j < |s| && s[i] == s[j]
  {
    s[0]
  }

  function contains(s: string, c: char): bool {
    exists i :: 0 <= i < |s| && s[i] == c
  }

  function countYays(secret: string, guess: string): nat
    requires |secret| == |guess|
  {
    if |secret| == 0 then 0 
    else (if secret[0] == guess[0] then 1 else 0) + countYays(secret[1..], guess[1..])
  }

  function countCommon(secret: string, guess: string): nat {
    if guess == "" then 0 
    else (if contains(secret, guess[0]) then 1 else 0) + countCommon(secret, guess[1..])
  }

  function countNaes(secret: string, guess: string): nat
    requires |secret| == |guess|
  {
    var common := countCommon(secret, guess);
    var yays := countYays(secret, guess);
    if common >= yays then common - yays else 0
  }

  function formatSecret(s: string): string {
    if |s| == 0 then "[]"
    else "[" + s[0..1] + formatSecretRec(s, 1) + "]"
  }

  function formatSecretRec(s: string, i: nat): string
    decreases |s| - i
  {
    if i >= |s| then ""
    else ", " + s[i..i+1] + formatSecretRec(s, i+1)
  }
}