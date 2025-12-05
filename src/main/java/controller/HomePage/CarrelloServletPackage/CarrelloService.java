package controller.HomePage.CarrelloServletPackage;

import controller.utils.Validator;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.utenteService.Utente;

import java.util.List;

public class CarrelloService {

    /**
     * Risultato della logica di business del carrello.
     * - se admin == true → l'utente è admin, la JSP sarà quella admin
     * - se admin == false → usare il campo "disponibile" ("si"/"no")
     */
    public static class Result {
        private final boolean admin;
        private final String disponibile; // può essere null se admin

        public Result(boolean admin, String disponibile) {
            this.admin = admin;
            this.disponibile = disponibile;
        }

        public boolean isAdmin() {
            return admin;
        }

        public String getDisponibile() {
            return disponibile;
        }
    }

    /**
     * Logica estratta dalla servlet:
     * - controlla se l'utente è admin
     * - se non è admin, scorre il carrello e determina "disponibile"
     */
    public Result preparaDati(Utente utente, Carrello carrello) {
        boolean isAdmin = Validator.checkIfUserAdmin(utente);
        if (isAdmin) {
            // per admin non calcoliamo il carrello
            return new Result(true, null);
        }

        String disponibile = "no";

        if (carrello != null) {
            List<RigaCarrello> righe = carrello.getRigheCarrello();
            if (righe != null) {
                for (RigaCarrello r : righe) {
                    if (r != null && r.getLibro() != null && r.getLibro().isDisponibile()) {
                        disponibile = "si";
                        break;
                    }
                }
            }
        }

        return new Result(false, disponibile);
    }
}

