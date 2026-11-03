// Verification service invoked from a Flow's actionCalls.
public with sharing class ContactVerification {
    private static final Integer CODE_LENGTH = 6;

    @InvocableMethod(label='Verify Contact' description='Checks a contact exists')
    public static void verify(List<Id> contactIds) {
        List<Contact> found = [SELECT Id, Email FROM Contact WHERE Id IN :contactIds];
        for (Contact c : found) {
            touch(c);
        }
    }

    @AuraEnabled(cacheable=true)
    public static Integer codeLength() {
        return CODE_LENGTH;
    }

    private static void touch(Contact c) {
        update c;
    }
}
