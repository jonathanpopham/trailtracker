// Exercises SOQL FROM-clause extraction (trailtracker-bug-soql-uses-type-uwl):
// custom __c objects, WHERE binds, aliases, child-relationship sub-selects
// (never lifted) and WHERE-clause semi-joins (inner SObject lifted).
public with sharing class ReferralQueries {
    public List<Referral__c> open(Id patientId) {
        return [
            SELECT Id, Patient__c
            FROM Referral__c
            WHERE Patient__c = :patientId AND Status__c != 'Closed'
            ORDER BY CreatedDate DESC
            LIMIT 50
        ];
    }

    public Integer wonCount() {
        return [SELECT COUNT() FROM Opportunity o WHERE o.StageName = 'Won'];
    }

    public List<Account> householdsWithContacts() {
        // `(SELECT … FROM Contacts)` names a child *relationship*, not an
        // SObject — only Account may be lifted.
        return [SELECT Id, (SELECT LastName FROM Contacts) FROM Account];
    }

    public List<Account> accountsWithActiveContacts() {
        // Semi-join: the inner FROM names a real SObject (Contact).
        return [SELECT Id FROM Account WHERE Id IN (SELECT AccountId FROM Contact WHERE Active__c = true)];
    }
}
