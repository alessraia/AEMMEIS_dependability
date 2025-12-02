package controller.admin.gestisciProdotti.ModificaLibro;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Sede;
import model.libroService.SedeDAO;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;

import java.util.ArrayList;
import java.util.List;

public class ModificaLibroService {
    private final LibroDAO libroDAO;
    private final SedeDAO sedeDAO;
    private final RepartoDAO repartoDAO;

    /**
     * Costruttore di default: usa i DAO reali.
     * Usato dalla servlet in produzione.
     */
    public ModificaLibroService() {
        this(new LibroDAO(), new SedeDAO(), new RepartoDAO());
    }

    /**
     * Costruttore alternativo: usato da test/benchmark
     * per iniettare DAO finti (in memoria).
     */
    public ModificaLibroService(LibroDAO libroDAO, SedeDAO sedeDAO, RepartoDAO repartoDAO) {
        this.libroDAO = libroDAO;
        this.sedeDAO = sedeDAO;
        this.repartoDAO = repartoDAO;
    }

    /**
     * Logica estratta dalla servlet:
     * - recupera il libro
     * - recupera sedi e reparti in cui è presente
     * - calcola sedi e reparti NON presenti
     *
     * @param isbn                      ISBN del libro
     * @param outSedi                   (output) sedi in cui il libro è presente
     * @param outSediNonPresenti        (output) sedi in cui il libro NON è presente
     * @param outReparti                (output) reparti in cui il libro è presente
     * @param outRepartiNonPresenti     (output) reparti in cui il libro NON è presente
     * @return il Libro corrispondente all'ISBN (può essere null se non trovato)
     */
    public Libro preparaDati(
            String isbn,
            List<Sede> outSedi,
            List<Sede> outSediNonPresenti,
            List<Reparto> outReparti,
            List<Reparto> outRepartiNonPresenti) {

        // Libro (in produzione normalmente non sarà null)
        Libro libro = libroDAO.doRetrieveById(isbn);

        // --- SEDI: logica come nella servlet originale ---
        List<Sede> sediPresenti = libroDAO.getPresenzaSede(isbn);
        List<Sede> sediNonPresenti = new ArrayList<>(sedeDAO.doRetrivedAll());
        for (int i = 0; i < sediNonPresenti.size(); i++) {
            Sede sede = sediNonPresenti.get(i);
            if (sediPresenti.contains(sede)) {
                sediNonPresenti.remove(i);
            }
        }

        // --- REPARTI: stessa logica ---
        List<Reparto> repartiPresenti = libroDAO.getAppartenenzaReparto(isbn);
        List<Reparto> repartiNonPresenti = new ArrayList<>(repartoDAO.doRetrivedAll());
        for (int i = 0; i < repartiNonPresenti.size(); i++) {
            Reparto reparto = repartiNonPresenti.get(i);
            if (repartiPresenti.contains(reparto)) {
                repartiNonPresenti.remove(i);
            }
        }

        // Riempio le liste "out"
        outSedi.clear();
        outSedi.addAll(sediPresenti);

        outSediNonPresenti.clear();
        outSediNonPresenti.addAll(sediNonPresenti);

        outReparti.clear();
        outReparti.addAll(repartiPresenti);

        outRepartiNonPresenti.clear();
        outRepartiNonPresenti.addAll(repartiNonPresenti);

        return libro;
    }
}

