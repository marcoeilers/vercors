
// implicit static_level 1;
//@ static_invariant Perm(Database.instance, 1\2) ** (Database.instance != null ==> Perm(Database.instance.data, write) ** Perm(Database.instance, read)) ** (Database.instance == null ==> Perm(Database.instance, 1\2));
class Database{
    private int data;
    private static Database instance = null;

    // implicit static level 1
    //@ decreases;
    //@ ensures Perm(data, write);
    private Database(){
        data = 0;
    }

    // implicit static level 1
    //@ context Perm(Database.instance, 1\4);
    //@ requires Database.instance == null ==> Perm(Database.instance, 3\4);
    //@ ensures \old(Database.instance) == null ==> (Perm(Database.instance, 1\2) ** Perm(Database.instance.data, write));
    //@ ensures \result == Database.instance;
    public static Database getInstance(){
        if (Database.instance == null)
            Database.instance = new Database();
        return Database.instance;
    }

    // implicit static level 1
    //@ requires Perm(data, read);
    public /*@ pure @*/ int getContents() {
        return data;
    }

}

// implicit static level 1
class Client {
    //@ static_level 3;
    public static void main(String[] args) {
        //@ openInv Database write;
        Database db = Database.getInstance();
        Database db2 = Database.getInstance();
        //@ assert db == db2;
        db.getContents();
        //@ closeInv Database write;
        //@ openInv Database write;
        Database db3 = Database.getInstance();
        db3.getContents();
        //@ closeInv Database write;
        //@ assert db == db3;
    }
}