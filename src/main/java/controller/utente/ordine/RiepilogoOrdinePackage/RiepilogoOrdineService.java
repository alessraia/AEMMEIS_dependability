package controller.utente.ordine.RiepilogoOrdinePackage;


import controller.utils.Validator;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.utenteService.Utente;

public class RiepilogoOrdineService {

    /**
     * Risultato della logica di business:
     * - se admin == true → l'utente è admin, non serve l'Ordine
     * - se admin == false → usare il campo ordine
     */
    public static class Result {
        private final boolean admin;
        private final Ordine ordine;

        public Result(boolean admin, Ordine ordine) {
            this.admin = admin;
            this.ordine = ordine;
        }

        public boolean isAdmin() {
            return admin;
        }

        public Ordine getOrdine() {
            return ordine;
        }
    }

    /**
     * Logica estratta dalla servlet:
     * - se l'utente è admin → segnala admin, non carica l'ordine
     * - altrimenti usa l'OrdineDAO per recuperare l'ordine
     */
    public Result preparaDati(Utente utente, String idOrdine, OrdineDAO ordineDAO) {
        if (Validator.checkIfUserAdmin(utente)) {
            // ramo admin: nessuna chiamata al DAO
            return new Result(true, null);
        }

        Ordine ordine = ordineDAO.doRetrieveById(idOrdine);
        return new Result(false, ordine);
    }
}
