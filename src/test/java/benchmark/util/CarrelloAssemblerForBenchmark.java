package benchmark.util;

import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;

import java.util.List;

/**
 * Helper usato SOLO nei benchmark JMH per simulare
 * la costruzione di un Carrello a partire da dati
 * già disponibili in memoria (id, totale, email, righe).
 *
 * Non accede al database, non usa ConPool, non usa Mockito.
 */
public class CarrelloAssemblerForBenchmark {

    public Carrello buildCarrello(String idCarrello,
                                  double totale,
                                  String email,
                                  List<RigaCarrello> righeCarrello) {

        Carrello carrello = new Carrello();
        carrello.setIdCarrello(idCarrello);
        carrello.setTotale(totale);
        carrello.setEmail(email);
        carrello.setRigheCarrello(righeCarrello);

        return carrello;
    }
}
