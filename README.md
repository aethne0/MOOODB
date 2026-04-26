# MOOODB

<img src="https://raw.githubusercontent.com/aethne0/MOOODB/refs/heads/master/cows.png" align="right" alt="Cow"/>

we strictly follow the 1 M and 3 Os of MOOODB:
1. [M]akes a new subtree on writes!
2. [O]n disk!
3. [O]rchestrates transactions!
4. [O]nly a fool would not believe in MOOODB!

are your btrees imoootable?

---
**MOOODB** is a copy-on-write, B+tree based relational database system, and is a work in progress. 
- Single writer, multiple reader - reads are not blocked by the writer.
- Durability is provided by copy-on-write, and readers see the most recent version of the DB until the current writer commits.
- In the event of a mid-tx crash, the most recent version of the DB will be intact.
- Uses B+trees for indicies and freelist, with heap pages for actual tuples (with the exception of covering indicies, like for the freelist).
- Storage engine is close to being in working order, then work will start on query planning & execution.
