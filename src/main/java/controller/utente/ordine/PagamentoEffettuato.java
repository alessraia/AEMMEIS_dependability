package controller.utente.ordine;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.ordineService.Ordine;
import model.tesseraService.TesseraDAO;
import model.utenteService.Utente;

import java.io.IOException;
import java.time.LocalDate;

@WebServlet("/pagamento-effettuato")
public class PagamentoEffettuato extends HttpServlet {
    private TesseraDAO tesseraDAO = new TesseraDAO();
    
    public void setTesseraDAO(TesseraDAO tesseraDAO) {
        this.tesseraDAO = tesseraDAO;
    }
    
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if (Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException e) {
                log("Errore durante il forward", e);
            } catch (IOException e) {
                log("Errore di I/O durante il forward", e);
            }
        }
        Ordine ordine = new Ordine();
        String address = null;
        //sto salvando sempre sulla request questi parametri poichè li devo mantenere fino a salvataggio ordine
        //dubbio sul metterlo direttamente in sessione...anche se non credo sia giusto salvarlo in sessione.
        ordine.setCitta(request.getParameter("citta"));
        ordine.setIndirizzoSpedizione(request.getParameter("indirizzo"));
        ordine.setCosto(Double.parseDouble(request.getParameter("costo")));

        int punti = 0;
        if(utente.getTipo().equalsIgnoreCase("premium")){
            String puntiString = request.getParameter("punti");

            if(isNumeric(puntiString)) {
                punti = Integer.parseInt(puntiString);
                if (punti < 0 || punti > tesseraDAO.doRetrieveByEmail(utente.getEmail()).getPunti()) {
                    RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
                    try {
                        dispatcher.forward(request, response);
                    } catch (ServletException e) {
                        log("Errore durante il forward", e);
                    } catch (IOException e) {
                        log("Errore di I/O durante il forward", e);
                    }
                    return;
                }
            }else if(!(puntiString.isEmpty())){
                RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
                try {
                    dispatcher.forward(request, response);
                } catch (ServletException e) {
                    log("Errore durante il forward", e);
                } catch (IOException e) {
                    log("Errore di I/O durante il forward", e);
                }
                return;
            }


        }
        ordine.setPuntiSpesi(punti);

        //effettuare controlli su dati dell'utente che acquista
        String cardName = request.getParameter("cardName");
        String cardNumber = request.getParameter("cardNumber");
        String expiryDate = request.getParameter("expiryDate");
        String cvv = request.getParameter("cvv");

        if(cardName==null || cardName.isEmpty() || !isNumeric(cardNumber) || expiryDate==null || /*isValidDate(expiryDate) ||*/ !isNumeric(cvv)){
            //pagina di errore per inserimento parametri errato
            address = "/WEB-INF/errorJsp/erroreForm.jsp";
            //response.sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");//forse

        }else{
            address = "/WEB-INF/results/ordineEffettuato.jsp";
            request.setAttribute("ordine", ordine);
        }

        RequestDispatcher dispatcher = request.getRequestDispatcher(address);
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward", e);
        }
    }

    private static boolean isNumeric(String str) {//metodo che utilizza espressione regolare per verificare che una stringa contenga solo numeri
        return str != null && !str.isEmpty() && str.matches("\\d+");
    }

    private boolean isValidDate(String dateStr) {
        try {
            LocalDate.parse(dateStr); // Prova a fare il parsing della stringa come LocalDate
            return true;
        }catch(Exception e){
            return false; // Se l'eccezione viene lanciata, la stringa non è una data valida
        }
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        this.doGet(req, resp);
    }
}