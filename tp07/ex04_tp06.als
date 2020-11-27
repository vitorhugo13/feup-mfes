//Animals = { (A0, {A1, A2}), (A1, {}) }

sig Animals{
    animalSpecies: one Species, //1. Every animal is of a single species.
    animalHabitat: lone Habitats,  //2. An animal of the Zoo may be, at most, in a single habitat.
    coExist: set Animals
}

/* alternative

sig Animals {
   animalsSpecies: Species
}

fact {
   #animalSpecies = 1
}
*/

fact{
    animalHabitat in Animals some->Habitats  //3. Each habitat has at least one animal.
    //ou #animalHabitat > 1
    {all h:Habitats | #animalHabitat.h =< 100} //4. Each habitat has at most 100 animals.
    // usamos relação.h e nao h.relação pois o dominio do tuplo é animal
    {all h:Habitats | all a1,a2:animalHabitat.h | a2 in a1.coExist}  //5. Each habitat may contain only animals that may coexist.
}
sig Species{
}

some sig Habitats{ //gerar sempre instancias que têm 1 ou + habitats (poderiamos meter o mesmo para os outros)
    veterinariesHabitat: set Veterinaries,
    coordinatorHabitat: one veterinariesHabitat  //7. Each habitat of the Zoo has a single coordinator.
                                                //10. The coordinator of an habitat is a veterinary of that habitat.
}


fact{
  coordinatorHabitat in Habitats lone-> Veterinaries  //8. Each veterinary can be at most coordinator of a single habitat.
    // all v: vetenarian | #coordinatorHabitat.v =< 1
  all v:Veterinaries | #veterinariesHabitat.v =<2  //12. Each veterinary is associated with at most 2 habitats.
}

sig Veterinaries{
    knowsCure: some Species  //6. Each veterinary knows how to cure at least one species of animals.
}

fact{
  knowsCure in Veterinaries some-> Species  //9. All species in the zoo have a veterinary that knows how to heal them.
  //ou all s:Species | some knowsCure.s
  all h:Habitats | 
    all v:h.veterinariesHabitat | 
    (animalHabitat.h).animalSpecies in v.knowsCure //11. The veterinaries associated with each habitat know how to heal all the species of the habitat.
}
run{}

// http://alloy4fun.inesctec.pt/yKcGasyiu6kgDGRXM

