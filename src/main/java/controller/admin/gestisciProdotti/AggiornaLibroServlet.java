package controller.admin.gestisciProdotti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Libro;
import model.libroService.LibroDAO;

import java.io.IOException;

@WebServlet("/aggiorna-libro")
public class AggiornaLibroServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        String titolo=request.getParameter("titolo");
        String isbn=request.getParameter("isbn");
        String annoPubb=request.getParameter("annoPubb");
        String genere=request.getParameter("genere");
        String prezzo1 = request.getParameter("prezzo");
        String sconto1 = (request.getParameter("sconto"));
        String trama=request.getParameter("trama");
        String immagine=request.getParameter("immagine");

        if(titolo == null || titolo.isEmpty() || isbn == null || annoPubb == null || annoPubb.isEmpty() ||
        genere == null || genere.isEmpty() || prezzo1 == null || trama == null || immagine == null) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
            dispatcher.forward(request, response);
            return;
        }

        double prezzo = 0;
        try{
            prezzo = Double.parseDouble(prezzo1);
        }catch (NumberFormatException e){
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
            dispatcher.forward(request, response);
            return;
        }

        int sconto = 0;
        if(isValid(sconto1))
            sconto = Integer.parseInt(sconto1);
        else {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
            dispatcher.forward(request, response);
            return;
        }

        LibroDAO libroService = new LibroDAO();
        Libro libro = new Libro();
        libro.setTitolo(titolo);
        libro.setIsbn(isbn);
        libro.setGenere(genere);
        libro.setAnnoPubblicazioni(annoPubb);
        libro.setPrezzo(prezzo);
        libro.setSconto(sconto);
        libro.setTrama(trama);
        libro.setImmagine(immagine);

        libroService.updateLibro(libro);
        RequestDispatcher dispatcher = request.getRequestDispatcher("modifica-libro");
        dispatcher.forward(request, response);
    }

    public boolean isValid(String str){
        return str.matches("\\d+");
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        this.doGet(req, resp);
    }
}
