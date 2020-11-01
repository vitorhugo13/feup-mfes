datatype Sex = Masculine | Feminine
datatype CivilState = Single | Married | Divorced | Widow | Dead
 
class Person
{
    const name: string; // ‘const’ for immutable fields
    const sex: Sex;
    const mother: Person?; // ‘?’ to allow null
    const father: Person?;
    var spouse: Person?;
    var civilState: CivilState;
 

    predicate Valid()
        reads this,spouse
    {
        (this.spouse != null <==> this.civilState == Married)
        && (this.mother != null ==> this.mother.sex == Feminine)
        && (this.father != null ==> this.father.sex == Masculine)
        && (this.spouse != null ==> this.spouse.sex != this.sex)
        && (this.spouse != null ==> this.spouse.spouse == this)
    }

    constructor (name: string, sex: Sex, mother: Person?, father: Person?)
        requires (father != null ==> father.sex == Masculine)
        requires (mother != null ==> mother.sex == Feminine)
        ensures Valid() 
        ensures this.name == name
        ensures this.sex == sex
        ensures this.mother == mother
        ensures this.father == father
        ensures this.spouse == null
        ensures this.civilState == Single
    {
        this.name := name;
        this.sex := sex;
        this.mother := mother;
        this.father := father;
        this.spouse := null;
        this.civilState := Single;
    }
 
    method marry(spouse: Person)
        modifies this, spouse

        requires Valid()
        requires this.civilState == Single
        requires spouse.sex != this.sex

        ensures Valid()
        ensures spouse.spouse == this
        ensures spouse.civilState == Married
        ensures this.spouse == spouse
        ensures this.civilState == Married

    {
        spouse.spouse := this;
        spouse.civilState := Married;
        this.spouse := spouse;
        this.civilState := Married;
    }
 
    method divorce()
        modifies this, spouse
        requires Valid()
        requires this.civilState == Married
        ensures Valid()

    {
        spouse.spouse := null;
        spouse.civilState := Divorced;
        this.spouse := null;
        this.civilState := Divorced;
    }
 
    method die()
        modifies this, spouse
        requires Valid()
        requires this.civilState != Dead
        ensures Valid()
    {
        if spouse != null
        {
            spouse.spouse := null;
            spouse.civilState := Widow;
        }
        this.spouse := null;
        this.civilState := Dead;
    }
}

method Main() {
    var person := new Person("vitor", Masculine, null, null);
    var person2 := new Person("catarina", Feminine, null, null);

    person.marry(person2);

    assert person.spouse == person2;
    assert person2.spouse == person;
    assert person.sex != person2.sex;
    
    //continuar a executar funções e a fazer asserts
}