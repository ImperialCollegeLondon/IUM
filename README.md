# Introduction to University Mathematics

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/ImperialCollegeLondon/IUM).

These are Lean files which relate to Imperial College London's Introduction to University Mathematics course. 

In 2022 I lectured Part I, and the files in the `2022` directory contain many basic examples and questions formalised in Lean.

I lectured Part II in 2023, and the files in the `2023` directory contain self-contained definitions of the integers and the rationals from "the ground up". 

Everything in `Old` is autoported from Lean 3 and may well not run without being fixed up.

### Remote running via GitPod

You don't need to install anything onto your computer to run this repo. Just click on the "Open in Gitpod" link above. I guess you'll need an account
at github.com for this to work.

IMPORTANT: the first time you try this, it can take up to 5 minutes. It's really important that you don't open any files or click on anything until you see the message
```text
Attempting to download 5149 file(s)
Downloaded: 5149 file(s) [attempted 5149/5149 = 100%] (100% success)
Decompressing 5149 file(s)
Unpacked in 26052 ms
Completed successfully!
```
at the bottom of the screen. In particular, opening a file in the repo before mathlib is fully downloaded may trigger a compilation of mathlib which will cause trouble.

Once you have this set-up working you can just bookmark the page and then it will start up essentially instantly.

### Local installation

You can install everything locally following the instructions [here](https://docs.lean-lang.org/lean4/doc/quickstart.html) (to install Lean)
and then [here](https://leanprover-community.github.io/install/project.html) (to install this project). 
