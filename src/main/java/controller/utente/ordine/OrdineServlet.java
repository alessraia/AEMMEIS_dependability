package controller.utente.ordine;


import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.carrelloService.CarrelloDAO;
import model.carrelloService.RigaCarrello;
import model.carrelloService.RigaCarrelloDAO;
import model.gestoreService.Gestore;
import model.gestoreService.GestoreDAO;
import model.libroService.Libro;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.ordineService.RigaOrdine;
import model.ordineService.RigaOrdineDAO;
import model.tesseraService.Tessera;
import model.tesseraService.TesseraDAO;
import model.utenteService.Utente;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.RoundingMode;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

@WebServlet("/do-ordine")
public class OrdineServlet extends HttpServlet {

    private OrdineDAO ordineDAO = new OrdineDAO();
    private CarrelloDAO carrelloDAO = new CarrelloDAO();
    private RigaCarrelloDAO rigaCarrelloDAO = new RigaCarrelloDAO();
    private TesseraDAO tesseraDAO = new TesseraDAO();
    private GestoreDAO gestoreDAO = new GestoreDAO();

    public void setRigaCarrelloDAO(RigaCarrelloDAO rigaCarrelloDAO) {
        this.rigaCarrelloDAO = rigaCarrelloDAO;
    }

    public void setCarrelloDAO(CarrelloDAO carrelloDAO) {
        this.carrelloDAO = carrelloDAO;
    }

    public void setOrdineDAO(OrdineDAO ordineDAO){
        this.ordineDAO = ordineDAO;
    }
    
    public void setTesseraDAO(TesseraDAO tesseraDAO) {
        this.tesseraDAO = tesseraDAO;
    }
    
    public void setGestoreDAO(GestoreDAO gestoreDAO) {
        this.gestoreDAO = gestoreDAO;
    }
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        //prendo ciò che ho in  sessione
        HttpSession session= request.getSession();
        if(Validator.checkIfUserAdmin((Utente) session.getAttribute("utente"))) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException e) {
                log("Errore durante il forward", e);
            } catch (IOException e) {
                log("Errore di I/O durante il forward", e);
            }
        }

        //non faccio il controllo poichè lo faccio negli step prima...quindi se non ci fossero righe non dovrebbe
        //proprio arrivare a questo punto.
        List<RigaCarrello> righeCarrello = (List<RigaCarrello>) session.getAttribute("righeDisponibili");

        Carrello carrello = (Carrello) session.getAttribute("carrello");
        Utente utente = (Utente) session.getAttribute("utente");

        //credo gli oggetti che mi serviranno e i relativi services
        Ordine ordine = new Ordine();
        //RigaOrdineDAO rigaOrdineDAO = new RigaOrdineDAO();
        Carrello carrelloDB = carrelloDAO.doRetriveByUtente(utente.getEmail());

        //parametri passati da servlet a jsp...
        ordine.setIndirizzoSpedizione(request.getParameter("indirizzo"));
        ordine.setCitta(request.getParameter("citta"));

       // if(utente.getTipo().equalsIgnoreCase("premium")){
        //setto i punti, se è un utente standard sono a 0
            String puntiString = request.getParameter("punti");
            int punti = 0;
            if(puntiString != null && !puntiString.isEmpty())
                punti = Integer.parseInt(puntiString);
            ordine.setPuntiSpesi(punti);
       // }



        //parametri calcolati
        double costo = 0;
        int puntiAcquisiti = 0;
        //creo idOrdine
        List<String> idOrdini = ordineDAO.doRetrivedAllByIdOrdini(); //mock
        String idOrdine;
        Random random =new Random();
        do {
            idOrdine = "T" + random.nextInt(10) + random.nextInt(10) + random.nextInt(10);
        }while(idOrdini.contains(idOrdine));
        ordine.setIdOrdine(idOrdine);


        List<RigaOrdine> righeOrdine = new ArrayList<RigaOrdine>();
        //prendo i libri selezionati dalle righe carrello e calcolo il costo e i punti

        for(RigaCarrello rigaCarrello : righeCarrello){
            Libro l = rigaCarrello.getLibro();
            RigaOrdine riga = new RigaOrdine();
            riga.setIdOrdine(ordine.getIdOrdine());
            riga.setLibro(l);

            double prezzoUnitarioPrima = (l.getPrezzo() - (l.getPrezzo()*l.getSconto()/100));
            BigDecimal bd = new BigDecimal(prezzoUnitarioPrima).setScale(2, RoundingMode.HALF_UP);
            double prezzoUnitario = bd.doubleValue();
            riga.setPrezzoUnitario(prezzoUnitario);
            riga.setQuantita(rigaCarrello.getQuantita());

        //    rigaOrdineDAO.doSave(riga); //salvo nel db la riga ordine
            righeOrdine.add(riga);

            costo += ((rigaCarrello.getQuantita() * prezzoUnitario) /*- (ordine.getPuntiSpesi() * 0.10)*/); //tolgo
            if(utente.getTipo().equalsIgnoreCase("premium"))
                puntiAcquisiti += 5* rigaCarrello.getQuantita();


            //quando scorro la lista delle righe del carrello che voglio acquistare
            //devo eventualmente cancellare la riga in sessione e nel db, o settare la quantità.
            for(int i=0; i<carrelloDB.getRigheCarrello().size(); i++){
                RigaCarrello rc = carrelloDB.getRigheCarrello().get(i);
                Libro libroRC = rc.getLibro();
                if(libroRC.equals(l)){
                    int differenza = rc.getQuantita() - rigaCarrello.getQuantita();
                    if (differenza <= 0){
                        rigaCarrelloDAO.deleteRigaCarrello(l.getIsbn(), carrelloDB.getIdCarrello());

                    }
                }
            }
            for(int j = 0; j<carrello.getRigheCarrello().size(); j++){
                RigaCarrello rigaInSessione = carrello.getRigheCarrello().get(j);
                if(rigaInSessione.getLibro().equals(l)){
                    carrello.getRigheCarrello().remove(j);
                    break;
                }
            }

        }

        ordine.setPuntiOttenuti(puntiAcquisiti);

        //aggiorno tessera
       if(utente.getTipo().equalsIgnoreCase("premium")){
           Tessera tessera = tesseraDAO.doRetrieveByEmail(utente.getEmail());
           if(tessera.getDataScadenza().isAfter(LocalDate.now())){
               tessera.setPunti(tessera.getPunti() - ordine.getPuntiSpesi() + ordine.getPuntiOttenuti());
                tesseraDAO.updateTessera(tessera);
            } else {
                ordine.setPuntiSpesi(0); //non può spendere punti poichè la tessera è scaduta.
            }
       }

        // ordine.setCosto(Double.parseDouble(request.getParameter("costo")));
        double costoAggiornato=costo - (ordine.getPuntiSpesi() * 0.10);
        BigDecimal bd = new BigDecimal(costoAggiornato).setScale(2, RoundingMode.HALF_UP);
        double costoArrotondato = bd.doubleValue();
        ordine.setCosto(costoArrotondato); //lo ricalcolo per sicurezza
            //utente che effettua l'ordine
        ordine.setEmail(utente.getEmail());
            //quando si fa l'ordine: nel momento di invocazione della servlet
        ordine.setDataEffettuazione(LocalDate.now());
            //righeOrdine
        ordine.setRigheOrdine(righeOrdine);

        ordine.setStato("In Lavorazione");
        Random rand = new Random();
        List<Gestore> gestoriDispo = gestoreDAO.doRetrivedAll();
        ordine.setMatricola(gestoriDispo.get(rand.nextInt(gestoriDispo.size())).getMatricola());

        ordineDAO.doSave(ordine);

        response.sendRedirect("index.html");
    }
}

