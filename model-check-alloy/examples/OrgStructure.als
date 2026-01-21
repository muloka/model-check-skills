/*
 * Organization Structure Model
 * 
 * Demonstrates relational constraints:
 *   - Every user belongs to exactly one organization
 *   - Every organization has at least one admin
 *   - Admins are users in that organization
 *
 * Run with: alloy exec OrgStructure.als
 */

module OrgStructure

--------------------------------------------------------------------------------
-- SIGNATURES
--------------------------------------------------------------------------------

sig Organization {
    members: set User,
    admins: set User
}

sig User {
    org: one Organization
}

--------------------------------------------------------------------------------
-- FACTS (constraints)
--------------------------------------------------------------------------------

-- Membership is consistent: user.org matches org.members
fact MembershipConsistent {
    all u: User, o: Organization | 
        u in o.members <=> u.org = o
}

-- Admins must be members of their organization
fact AdminsAreMembers {
    all o: Organization | o.admins in o.members
}

-- Every organization has at least one admin
fact AtLeastOneAdmin {
    all o: Organization | some o.admins
}

--------------------------------------------------------------------------------
-- ASSERTIONS
--------------------------------------------------------------------------------

-- No user can be in multiple organizations
assert SingleOrg {
    all u: User | one u.org
}

-- Every admin belongs to the org they admin
assert AdminBelongsToOrg {
    all o: Organization, u: o.admins | u.org = o
}

-- An organization with members has at least one admin
assert MembersImpliesAdmin {
    all o: Organization | some o.members => some o.admins
}

-- There are no orphan users (users without an org)
assert NoOrphanUsers {
    all u: User | some u.org
}

--------------------------------------------------------------------------------
-- COMMANDS
--------------------------------------------------------------------------------

check SingleOrg for 5
check AdminBelongsToOrg for 5
check MembersImpliesAdmin for 5
check NoOrphanUsers for 5

-- Generate example instances
run ShowSmallOrg {
    #Organization = 1
    #User = 3
} for 5

run ShowMultipleOrgs {
    #Organization = 2
    some o1, o2: Organization | o1 != o2 and #o1.members > 1 and #o2.members > 1
} for 6
