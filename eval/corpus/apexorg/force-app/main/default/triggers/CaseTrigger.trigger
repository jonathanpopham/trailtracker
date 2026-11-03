trigger CaseTrigger on Case (before insert, before update, after insert) {
    List<Account> owners = [SELECT Id, Name FROM Account];
    for (Case c : Trigger.new) {
        System.debug('processing ' + c.Id);
    }
}
