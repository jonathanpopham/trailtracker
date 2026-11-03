// Exercises the Apex call graph + DML tracking (TT-80).
public with sharing class CaseService {
    public void createContact() {
        insert new Contact(LastName = 'Doe');
    }

    public void closeCase(Case existing) {
        update existing;
    }

    public void process(List<Case> cases) {
        for (Case c : cases) {
            closeCase(c);
        }
        ContactVerification.verify(new List<Id>());
    }
}
