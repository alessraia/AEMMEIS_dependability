package model.carrelloService;

import model.libroService.Libro;

public class AggiornaCarrelloService {

    /**
     * Aggiorna la quantità del libro con l'ISBN specificato all'interno del carrello.
     *
     * @param carrello carrello da aggiornare (non nullo)
     * @param isbn     ISBN del libro da cercare (non nullo né vuoto)
     * @param quantity nuova quantità (>= 0)
     * @return true se l'elemento è stato trovato e aggiornato, false altrimenti
     * @throws IllegalArgumentException se i parametri non rispettano i vincoli
     */
    public boolean aggiornaQuantita(Carrello carrello, String isbn, int quantity) {
        if (carrello == null) {
            throw new IllegalArgumentException("Carrello nullo");
        }
        if (isbn == null || isbn.isEmpty()) {
            throw new IllegalArgumentException("ISBN non valido");
        }
        if (quantity < 0) {
            throw new IllegalArgumentException("Quantità negativa");
        }
        if (carrello.getRigheCarrello() == null) {
            return false;
        }

        boolean itemFound = false;
        for (RigaCarrello riga : carrello.getRigheCarrello()) {
            Libro libro = riga.getLibro();
            if (libro != null && isbn.equals(libro.getIsbn())) {
                riga.setQuantita(quantity);
                itemFound = true;
                break;
            }
        }
        return itemFound;
    }
}
