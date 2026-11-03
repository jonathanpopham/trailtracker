// Apex invocable target the ContactIntake flow's actionCalls resolves to (TT-62).
public with sharing class ContactVerifier {
    @InvocableMethod(label='Verify Contact' description='Checks a contact exists')
    public static void verifyContact(List<Id> contactIds) {
        List<Contact> found = [SELECT Id, Email FROM Contact WHERE Id IN :contactIds];
        System.debug(found.size());
    }
}
