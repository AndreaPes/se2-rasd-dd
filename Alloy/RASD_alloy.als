////////////////////////// SIGNATURES ////////////////////////////

abstract sig User {
    email: one Mail,
}

sig Student extends User {
    var applied: set Internship, 
    var work: lone Internship, 
    var cv: lone CV,
    university: one University
}

sig Internship {
    at: one Company,
    var rejected: set Student
}

sig Company extends User {}
sig University extends User {}

sig Mail {}
var sig CV {}

////////////////////////// CONSTRAINTS ///////////////////////////

// Internship's constraints

// Only one student can work in a single internship
fact OneStudentxInternship {
    all i: Internship | lone s: Student | i in s.work
}

// If a student is rejected from an internship, 
// they must have applied to it
fact RejectedimpliesApplied {
    all i: Internship | all r: i.rejected | i in r.applied 
}

// A student can only work in an internship 
// if they previously applied to it
fact PreviouslyAppliedifWorking {
    always (all s: Student | all i: Internship | i in s.work 
			implies once before i in s.applied)
}

// A student can only be rejected from an internship
//  if they previously applied to it
fact PreviouslyAppliedifRejected {
    always (all s: Student | all i: Internship | s in i.rejected 
			implies once before i in s.applied)
}

// User's Constraints

// No two users can have the same email address
fact noSameMail {
    all m: Mail | one u: User | m in u.email
}

// Student's constraints

// A student cannot apply for an internship without a CV, 
// and each student can have only one CV
fact studentCV {
    always (all s: Student | s.cv = none implies no s.applied)
}

// Every student must have a unique CV
fact noCV {
    always (all s: Student | s.cv != none 
			implies always (s.cv != none))
    always (all c: CV | one s: Student | c in s.cv)
}

// Historical constraint: Every CV must have belonged 
// to exactly one student
fact historicalCV {
    always (all c: CV | one s: Student | historically c in s.cv)
}

///////////////////////////// PREDICATES ///////////////////////////

// Control flow events to define the system's behavior
fact eventsFact {
    world
    always (
        all s: Student | stutterStudent[s] or
        (some i: s.applied | startWork[s, i]) or 
        (some i: Internship - s.applied | applyInt[s, i])
    )
    always (
        all i: Internship | stutterInternship[i] or
        (some s: applied.i | rejStudent[s, i])
    )
    always (
        some s: Student | stutterCV[s]
    )
}

// Nothing changes for a student
pred stutterStudent[s: Student] {
    s.applied' = s.applied
    s.work' = s.work
}

// Nothing changes for a student's CV
pred stutterCV[s: Student] {
    s.cv' = s.cv
}

// Nothing changes for an internship
pred stutterInternship[i: Internship] {
    i.rejected' = i.rejected
}

// A student starts working on an internship
pred startWork[s: Student, i: Internship] {
    s.cv != none
    i in s.applied
    s.work' = i and s.work = none
    s.applied' = s.applied
    s not in i.rejected'
    all s2: Student - s | i in s2.applied 
		implies s2 in i.rejected'
}

// A student applies for an internship
pred applyInt[s: Student, i: Internship] {
    s.work = none
    all st: Student - s | i not in st.work
    s.applied' = s.applied + i
    s.work' = s.work
}

// A student is rejected from an internship
pred rejStudent[s: Student, i: Internship] {
    s.work = none
    all st: Student - s | i not in st.work
    i.rejected' = i.rejected + s
}

// World constraints to initialize the system
pred world {
    #Student > 2
    #Company > 2
    #Internship > 2
    #Student.cv = 0
}

run {} for 10
